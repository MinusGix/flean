import Flean.IntegerEquivalence.ReluBits
import Flean.Operations.ExactIntBound
import Flean.Operations.PolicySoundInstances

/-! # A range-conditioned FP reduction of a concrete XOR network

This file is the first literal network in Flean's reductionist thread.  On Boolean inputs, consider
the fixed two-hidden-unit ReLU network

```text
h₁  = ReLU(x + y)
h₂  = ReLU(x + y - 1)
out = h₁ - 2 h₂.
```

Every affine operation below is the actual Flean floating-point operation, carried through
`ExactIntB`; `relu` is the actual sign-bit-dispatch `Fp.fpRelu`.  A single capacity hypothesis
`4 < 2^prec` licenses the whole trace.  The headline theorem identifies its final exact integer
with Boolean XOR.
-/

set_option autoImplicit false

/-! ## A bounded exact-integer ReLU

`ExactIntB` already carries actual add/subtract/multiply operations.  ReLU is exact on integers but
is not an arithmetic homomorphism, so its shadow is `max 0 n`; its concrete float is still exactly
the result of `Fp.fpRelu`.
-/

namespace ExactIntB

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Tighten a running magnitude bound without changing the represented float or integer. -/
def withBound (a : ExactIntB R) (bound : ℕ) (hbound : a.n.natAbs ≤ bound) : ExactIntB R where
  toExactInt := a.toExactInt
  bound := bound
  hbound := hbound

@[simp] theorem withBound_n (a : ExactIntB R) (bound hbound) :
    (a.withBound bound hbound).n = a.n := rfl

@[simp] theorem withBound_fp (a : ExactIntB R) (bound hbound) :
    (a.withBound bound hbound).fp = a.fp := rfl

@[simp] theorem withBound_bound (a : ExactIntB R) (bound hbound) :
    (a.withBound bound hbound).bound = bound := rfl

@[simp] theorem zero_n : (0 : ExactIntB R).n = 0 := rfl

@[simp] theorem one_n : (1 : ExactIntB R).n = 1 := rfl

/-- ReLU on a bounded exact integer.  The data field is the concrete sign-bit FP operation; the
integer shadow is `max 0 n`. -/
def relu (a : ExactIntB R) : ExactIntB R where
  toExactInt := {
    fp := (Fp.fpRelu (Fp.finite a.fp)).toFiniteOr0
    n := max 0 a.n
    agree := by
      rw [Fp.fpRelu_finite_eq, Fp.toFiniteOr0_finite]
      rw [Fp.fpRelu_finite_inner_toVal, a.agree]
      by_cases hn : 0 ≤ a.n
      · have hnR : (0 : R) ≤ (a.n : R) := by exact_mod_cast hn
        rw [max_eq_right hn, max_eq_right hnR]
      · have hnZ : a.n ≤ 0 := le_of_not_ge hn
        have hnR : (a.n : R) ≤ 0 := by exact_mod_cast hnZ
        rw [max_eq_left hnZ, max_eq_left hnR, Int.cast_zero]
  }
  bound := a.bound
  hbound := by
    by_cases hn : 0 ≤ a.n
    · rw [max_eq_right hn]
      exact a.hbound
    · rw [max_eq_left (le_of_not_ge hn), Int.natAbs_zero]
      exact Nat.zero_le _

@[simp] theorem relu_n (a : ExactIntB R) : a.relu.n = max 0 a.n := rfl

@[simp] theorem relu_bound (a : ExactIntB R) : a.relu.bound = a.bound := rfl

@[simp] theorem relu_fp (a : ExactIntB R) :
    a.relu.fp = (Fp.fpRelu (Fp.finite a.fp)).toFiniteOr0 := rfl

end ExactIntB

namespace Flean.RangeReduction.XorNet

/-! ## Boolean inputs and the integer circuit -/

/-- The integer encoded by a Boolean bit. -/
def bitInt (b : Bool) : ℤ := if b then 1 else 0

/-- The natural magnitude bound of a Boolean bit. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitInt_false : bitInt false = 0 := rfl
@[simp] theorem bitInt_true : bitInt true = 1 := rfl

@[simp] theorem bitNat_false : bitNat false = 0 := rfl
@[simp] theorem bitNat_true : bitNat true = 1 := rfl

/-- The algebraic XOR identity on Boolean integers. -/
theorem bitInt_xor (x y : Bool) :
    bitInt (x ^^ y) = bitInt x + bitInt y - 2 * (bitInt x * bitInt y) := by
  cases x <;> cases y <;> decide

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A Boolean bit as the exact floating-point integer zero or one, with its tight bound. -/
def bit (b : Bool) : ExactIntB R := if b then 1 else 0

@[simp] theorem bit_n (b : Bool) : (bit (R := R) b).n = bitInt b := by
  cases b <;> rfl

@[simp] theorem bit_bound (b : Bool) : (bit (R := R) b).bound = bitNat b := by
  cases b <;> rfl

@[simp] theorem bit_fp (b : Bool) :
    (bit (R := R) b).fp = if b then (1 : FiniteFp) else 0 := by
  cases b <;> rfl

/-! ## The concrete network

The definitions use a single capacity hypothesis for the largest propagated bound.  Smaller
intermediate obligations are discharged from it locally, so callers see one range/format contract.
-/

section Network

variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

variable (hcap : 4 < 2 ^ FloatFormat.prec.toNat)
  (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp)

/-- Shared pre-activation `x+y`. -/
def sum (x y : Bool) : ExactIntB R :=
  (bit (R := R) x).add (bit (R := R) y) (by
    rw [bit_bound, bit_bound]
    cases x <;> cases y <;> simp [bitNat]
    all_goals omega
  ) h_exp

@[simp] theorem sum_n (x y : Bool) :
    (sum (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = bitInt x + bitInt y := by
  simp [sum]

@[simp] theorem sum_bound (x y : Bool) :
    (sum (R := R) (hcap := hcap) (h_exp := h_exp) x y).bound = bitNat x + bitNat y := by
  simp [sum]

/-- First hidden unit: `ReLU(x+y)`. -/
def orCount (x y : Bool) : ExactIntB R :=
  (sum (R := R) (hcap := hcap) (h_exp := h_exp) x y).relu

@[simp] theorem orCount_n (x y : Bool) :
    (orCount (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = bitInt x + bitInt y := by
  cases x <;> cases y <;> simp [orCount, bitInt]

/-- Second pre-activation: `x+y-1`. -/
def andPre (x y : Bool) : ExactIntB R :=
  (sum (R := R) (hcap := hcap) (h_exp := h_exp) x y).sub 1 (by
    rw [sum_bound, ExactIntB.one_bound]
    cases x <;> cases y <;> simp [bitNat] <;> omega
  ) h_exp

@[simp] theorem andPre_n (x y : Bool) :
    (andPre (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = bitInt x + bitInt y - 1 := by
  simp [andPre]

/-- The second hidden unit, tightened to its semantic range `{0,1}`. -/
def andGate (x y : Bool) : ExactIntB R :=
  ExactIntB.withBound
    (andPre (R := R) (hcap := hcap) (h_exp := h_exp) x y).relu
    (bitNat (x && y)) (by
      cases x <;> cases y <;> simp [andPre, bitNat])

@[simp] theorem andGate_n (x y : Bool) :
    (andGate (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = bitInt (x && y) := by
  cases x <;> cases y <;> simp [andGate, andPre, bitInt]

@[simp] theorem andGate_bound (x y : Bool) :
    (andGate (R := R) (hcap := hcap) (h_exp := h_exp) x y).bound = bitNat (x && y) := by
  simp [andGate]

/-- The exact weight two, constructed once through the actual FP addition `1+1`. -/
def two : ExactIntB R := (1 : ExactIntB R).add 1 (by
  simpa using lt_trans (by decide : 2 < 4) hcap
  ) h_exp

@[simp] theorem two_n : (two (R := R) (hcap := hcap) (h_exp := h_exp)).n = 2 := rfl

@[simp] theorem two_bound : (two (R := R) (hcap := hcap) (h_exp := h_exp)).bound = 2 := rfl

/-- The scaled AND channel `2*h₂`. -/
def twiceAnd (x y : Bool) : ExactIntB R :=
  (andGate (R := R) (hcap := hcap) (h_exp := h_exp) x y).mul
    (two (R := R) (hcap := hcap) (h_exp := h_exp)) (by
    rw [andGate_bound, two_bound]
    cases x <;> cases y <;> simp [bitNat]
    all_goals omega
  ) h_exp

@[simp] theorem twiceAnd_n (x y : Bool) :
    (twiceAnd (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = 2 * bitInt (x && y) := by
  cases x <;> cases y <;> simp [twiceAnd, bitInt]

@[simp] theorem twiceAnd_bound (x y : Bool) :
    (twiceAnd (R := R) (hcap := hcap) (h_exp := h_exp) x y).bound =
      bitNat (x && y) * 2 := by
  simp [twiceAnd]

/-- The complete concrete FP network, carried with its exact integer reduction. -/
def eval (x y : Bool) : ExactIntB R :=
  (orCount (R := R) (hcap := hcap) (h_exp := h_exp) x y).sub
    (twiceAnd (R := R) (hcap := hcap) (h_exp := h_exp) x y) (by
    rw [orCount, ExactIntB.relu_bound, sum_bound, twiceAnd_bound]
    cases x <;> cases y <;> simp [bitNat]
    all_goals omega
  ) h_exp

/-- **Integer reduction.** The FP network's exact integer shadow is the familiar arithmetic XOR
circuit `x+y-2xy`. -/
theorem eval_n_eq_arithmetic_xor (x y : Bool) :
    (eval (R := R) (hcap := hcap) (h_exp := h_exp) x y).n =
      bitInt x + bitInt y - 2 * (bitInt x * bitInt y) := by
  cases x <;> cases y <;> simp [eval, bitInt]

/-- **Headline: the concrete floating-point network reduces to Boolean XOR.** -/
@[simp] theorem eval_n_eq_xor (x y : Bool) :
    (eval (R := R) (hcap := hcap) (h_exp := h_exp) x y).n = bitInt (x ^^ y) := by
  rw [eval_n_eq_arithmetic_xor, ← bitInt_xor]

/-! ## The literal floating-point trace

This definition erases the integer certificates and displays the operation sequence directly.
`eval_fp_eq_trace` proves that the reduction above did not replace any FP operation.
-/

/-- A Boolean input's literal finite FP value. -/
def fpBit (b : Bool) : FiniteFp := if b then 1 else 0

/-- The concrete FP operation trace, including extraction of the finite result after every op. -/
def fpEval (x y : Bool) : FiniteFp :=
  let s := (fpBit x + fpBit y).toFiniteOr0
  let h₁ := (Fp.fpRelu (Fp.finite s)).toFiniteOr0
  let p₂ := (s - (1 : FiniteFp)).toFiniteOr0
  let h₂ := (Fp.fpRelu (Fp.finite p₂)).toFiniteOr0
  let twoFp := ((1 : FiniteFp) + (1 : FiniteFp)).toFiniteOr0
  let twoH₂ := (h₂ * twoFp).toFiniteOr0
  (h₁ - twoH₂).toFiniteOr0

/-- Erasing the certificates from `eval` yields exactly the displayed FP trace. -/
theorem eval_fp_eq_trace (x y : Bool) :
    (eval (R := R) (hcap := hcap) (h_exp := h_exp) x y).fp = fpEval x y := by
  cases x <;> cases y <;> rfl

/-- The decoded real value of the literal FP trace is the encoded XOR bit. -/
theorem fpEval_toVal_eq_xor
    (hcap' : 4 < 2 ^ FloatFormat.prec.toNat)
    (h_exp' : FloatFormat.prec - 1 ≤ FloatFormat.max_exp)
    (x y : Bool) :
    ((fpEval x y).toVal : R) = (bitInt (x ^^ y) : R) := by
  rw [← eval_fp_eq_trace (R := R) (hcap := hcap') (h_exp := h_exp')]
  exact (eval (R := R) (hcap := hcap') (h_exp := h_exp') x y).agree.trans
    (by rw [eval_n_eq_xor])

end Network

end Flean.RangeReduction.XorNet
