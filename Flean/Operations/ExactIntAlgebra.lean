import Flean.Operations.ExactIntZero

/-! # An algebra of exactly-representable integers

`ExactInt.lean` / `ExactIntZero.lean` prove each float op on integer-valued floats is exact
(per op) — but every such lemma returns an `∃ f, op = f ∧ f.toVal = n`, so chaining them by
hand drags a pile of existential witnesses and intermediate equalities.

This file removes that friction by carrying the float as **honest data** rather than an
existential witness. An `ExactInt R` bundles:

* `fp` — the literal `FiniteFp` value (data, never hidden behind `∃`),
* `n`  — the integer it represents,
* `agree` — the proof `fp.toVal = n`.

The float operations become operations on `ExactInt`, and the projection `.n : ExactInt R
→ ℤ` *commutes with every one of them*: `(a.mul b _).n = a.n * b.n`, `(a + b).n = ...`,
`(-a).n = -a.n`, `(0).n = 0`, `(1).n = 1` — all by construction. That homomorphism law
**is** the reduction "the float computation is the integer computation", stated once.

`Neg`/`Zero`/`One` are *total* (negation can't overflow a representable integer), so they
are genuine Lean instances. `mul`/`add`/`sub` stay partial `def`s taking a magnitude bound
(overflow forbids total `Mul`/`Add` instances — which is the honest state of affairs:
`ExactInt` models `ℤ ∩ (-2^prec, 2^prec)`, closed under negation but not under +/×). The
ops take **no `≠ 0` side condition**: they route through the zero-admitting `_int_exact0`
lemmas, so a zero result is welcome (cancellation, zero weight/input).

DEFERRED (later): **running magnitude bound.** Carry one `|n| ≤ B` in the structure and
derive the per-op `< 2^prec` conditions from it — the start of the interval layer.
-/

namespace Fp

variable [FloatFormat]

/-- Total extraction of the underlying `FiniteFp` from an `Fp`, defaulting to `0` on the
non-finite branches. Lets us carry an op's *output* as literal `FiniteFp` data (the op
returns `Fp`); under a finiteness proof the default branch is never taken. -/
def toFiniteOr0 : Fp → FiniteFp
  | .finite f => f
  | _ => 0

@[simp] theorem toFiniteOr0_finite (f : FiniteFp) : (Fp.finite f).toFiniteOr0 = f := rfl

/-- A finite `Fp` is recovered from its `toFiniteOr0` extraction. Lets a consumer carry an
op output as data given only a finiteness Prop (no explicit witness float). -/
theorem eq_finite_toFiniteOr0 {x : Fp} (h : x.isFinite) : x = Fp.finite x.toFiniteOr0 := by
  cases x with
  | finite f => rfl
  | infinite b => simp [Fp.isFinite] at h
  | NaN => simp [Fp.isFinite] at h

end Fp

/-- A float paired with the integer it represents exactly. The `fp` value is honest data,
not an existential witness. Models `ℤ ∩ (-2^prec, 2^prec)` viewed as floats. -/
structure ExactInt (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  /-- The literal float value. -/
  fp : FiniteFp
  /-- The integer it represents. -/
  n : ℤ
  /-- Agreement: the float's real value is the integer. -/
  agree : (fp.toVal : R) = (n : R)

namespace ExactInt

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Total structure: the part of the algebra with no overflow side-conditions -/

instance : Zero (ExactInt R) := ⟨⟨0, 0, by rw [FiniteFp.toVal_zero, Int.cast_zero]⟩⟩

instance : One (ExactInt R) := ⟨⟨1, 1, by rw [FiniteFp.toVal_one, Int.cast_one]⟩⟩

instance : Neg (ExactInt R) :=
  ⟨fun a => ⟨-a.fp, -a.n, by rw [FiniteFp.toVal_neg_eq_neg, a.agree, Int.cast_neg]⟩⟩

@[simp] theorem zero_n : (0 : ExactInt R).n = 0 := rfl
@[simp] theorem one_n : (1 : ExactInt R).n = 1 := rfl
@[simp] theorem neg_n (a : ExactInt R) : (-a).n = -a.n := rfl

/-! ## Partial ops: multiply / add / subtract under a no-overflow bound -/

variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

/-- Exact multiplication of `ExactInt`s, when the integer product is representable in
`(-2^prec, 2^prec)` (zero allowed). The result's `fp` is literally the float `a.fp * b.fp`
computes. -/
def mul (a b : ExactInt R)
    (hbound : (a.n * b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactInt R where
  fp := (a.fp * b.fp).toFiniteOr0
  n := a.n * b.n
  agree := by
    obtain ⟨f, hf_eq, hf_val⟩ :=
      fpMulFinite_int_exact0 (R := R) a.fp b.fp a.n b.n a.agree b.agree hbound h_exp
    rw [hf_eq]; simp only [Fp.toFiniteOr0_finite]; exact hf_val

/-- Exact addition of `ExactInt`s, when the integer sum is representable in
`(-2^prec, 2^prec)` (zero allowed). -/
def add (a b : ExactInt R)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactInt R where
  fp := (a.fp + b.fp).toFiniteOr0
  n := a.n + b.n
  agree := by
    obtain ⟨f, hf_eq, hf_val⟩ :=
      fpAddFinite_int_exact0 (R := R) a.fp b.fp a.n b.n a.agree b.agree hbound h_exp
    rw [hf_eq]; simp only [Fp.toFiniteOr0_finite]; exact hf_val

/-- Exact subtraction of `ExactInt`s, when the integer difference is representable in
`(-2^prec, 2^prec)` (zero allowed). -/
def sub (a b : ExactInt R)
    (hbound : (a.n - b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactInt R where
  fp := (a.fp - b.fp).toFiniteOr0
  n := a.n - b.n
  agree := by
    obtain ⟨f, hf_eq, hf_val⟩ :=
      fpSubFinite_int_exact0 (R := R) a.fp b.fp a.n b.n a.agree b.agree hbound h_exp
    rw [hf_eq]; simp only [Fp.toFiniteOr0_finite]; exact hf_val

/-! ## The homomorphism `.n` and the provenance bridges `.fp`

`.n` commuting with the ops is the reduction itself, and holds definitionally. The `.fp`
bridges record that the structure's float is *exactly* what the underlying op computes —
no information is invented. -/

@[simp] theorem mul_n (a b : ExactInt R) (hbound h_exp) :
    (a.mul b hbound h_exp).n = a.n * b.n := rfl
@[simp] theorem add_n (a b : ExactInt R) (hbound h_exp) :
    (a.add b hbound h_exp).n = a.n + b.n := rfl
@[simp] theorem sub_n (a b : ExactInt R) (hbound h_exp) :
    (a.sub b hbound h_exp).n = a.n - b.n := rfl

theorem mul_fp (a b : ExactInt R) (hbound h_exp) :
    ((a.mul b hbound h_exp).fp : Fp) = fpMulFinite a.fp b.fp := by
  obtain ⟨f, hf_eq, _⟩ :=
    fpMulFinite_int_exact0 (R := R) a.fp b.fp a.n b.n a.agree b.agree hbound h_exp
  have hfp : (a.mul b hbound h_exp).fp = f := by
    show (a.fp * b.fp).toFiniteOr0 = f
    rw [hf_eq, Fp.toFiniteOr0_finite]
  rw [hfp]; exact hf_eq.symm

theorem add_fp (a b : ExactInt R) (hbound h_exp) :
    ((a.add b hbound h_exp).fp : Fp) = fpAddFinite a.fp b.fp := by
  obtain ⟨f, hf_eq, _⟩ :=
    fpAddFinite_int_exact0 (R := R) a.fp b.fp a.n b.n a.agree b.agree hbound h_exp
  have hfp : (a.add b hbound h_exp).fp = f := by
    show (a.fp + b.fp).toFiniteOr0 = f
    rw [hf_eq, Fp.toFiniteOr0_finite]
  rw [hfp]; exact hf_eq.symm

/-! ## The payoff: the "after" of `fpDot2Finite_int_exact`

The length-2 integer dot product is now a single `ExactInt` term — no `∃` threading, no
intermediate-equality pile — and its integer value is the integer dot product *by `rfl`*. -/

/-- Length-2 dot product as one `ExactInt` — one composed term, no `∃` threading and (now)
no `≠ 0` side conditions: only that each product and the sum are representable. -/
def dot2 (a₁ b₁ a₂ b₂ : ExactInt R)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactInt R :=
  (a₁.mul b₁ h₁b h_exp).add (a₂.mul b₂ h₂b h_exp) hsb h_exp

/-- The reduction, stated and proved by `rfl`: the float dot product's integer value is the
integer dot product. -/
@[simp] theorem dot2_n (a₁ b₁ a₂ b₂ : ExactInt R) (h₁b h₂b hsb h_exp) :
    (dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp).n
      = a₁.n * b₁.n + a₂.n * b₂.n := rfl

end ExactInt
