import Flean.Operations.ExactIntAlgebra

/-! # Magnitude-bounded exact integers — the interval layer

`ExactInt` proves a computation reduces to integer arithmetic *given* a per-op
representability bound `|result| < 2^prec`. Supplying those bounds by hand is the
bookkeeping that `dot2` still drags around (three separate `< 2^prec` arguments).

`ExactIntB R` adds a **running magnitude bound**: it bundles an `ExactInt R` with a `bound :
ℕ` and a proof `|n| ≤ bound`. The bound *propagates* through the operations —

  mul: `bound = bₐ · b_b`     add/sub: `bound = bₐ + b_b`     neg: `bound = bₐ`

— and each op derives its `< 2^prec` representability from the propagated bound (via
`Int.natAbs_mul` / `Int.natAbs_add_le`), so the caller supplies a bound on the *bound*, not
on the realized integer.

This is the start of interval analysis: the bound is what licenses the exactness, and it
flows forward with the computation. The payoff (`dot2` below): a length-2 dot product now
takes a **single** representability hypothesis `bₐ₁·b_b₁ + bₐ₂·b_b₂ < 2^prec` — it implies
each product fits *and* the sum fits, because the summands are nonnegative.
-/

/-- An `ExactInt` carrying a magnitude bound `|n| ≤ bound` that propagates through ops. -/
structure ExactIntB (R : Type*) [FloatFormat] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] extends ExactInt R where
  /-- A magnitude bound on the represented integer. -/
  bound : ℕ
  /-- The bound is valid. -/
  hbound : toExactInt.n.natAbs ≤ bound

namespace ExactIntB

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Total structure -/

instance : Zero (ExactIntB R) := ⟨⟨0, 0, by simp⟩⟩
instance : One (ExactIntB R) := ⟨⟨1, 1, by simp⟩⟩
instance : Neg (ExactIntB R) :=
  ⟨fun a => ⟨-a.toExactInt, a.bound, by simpa [Int.natAbs_neg] using a.hbound⟩⟩

@[simp] theorem zero_bound : (0 : ExactIntB R).bound = 0 := rfl
@[simp] theorem one_bound : (1 : ExactIntB R).bound = 1 := rfl
@[simp] theorem neg_bound (a : ExactIntB R) : (-a).bound = a.bound := rfl

/-! ## Bounded ops: representability is derived from the bound -/

variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

/-- Bounded multiplication: the caller bounds the *product of bounds*; representability of
the realized product is derived. Result bound is `a.bound * b.bound`. -/
def mul (a b : ExactIntB R)
    (hb : a.bound * b.bound < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactIntB R where
  toExactInt := a.toExactInt.mul b.toExactInt
    (by rw [Int.natAbs_mul]; exact lt_of_le_of_lt (Nat.mul_le_mul a.hbound b.hbound) hb) h_exp
  bound := a.bound * b.bound
  hbound := by
    rw [ExactInt.mul_n, Int.natAbs_mul]; exact Nat.mul_le_mul a.hbound b.hbound

/-- Bounded addition: result bound is `a.bound + b.bound`. -/
def add (a b : ExactIntB R)
    (hb : a.bound + b.bound < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactIntB R where
  toExactInt := a.toExactInt.add b.toExactInt
    (lt_of_le_of_lt (le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add a.hbound b.hbound)) hb) h_exp
  bound := a.bound + b.bound
  hbound := by
    rw [ExactInt.add_n]; exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add a.hbound b.hbound)

/-- Bounded subtraction: result bound is `a.bound + b.bound`. -/
def sub (a b : ExactIntB R)
    (hb : a.bound + b.bound < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactIntB R where
  toExactInt := a.toExactInt.sub b.toExactInt
    (lt_of_le_of_lt (le_trans (Int.natAbs_sub_le _ _) (Nat.add_le_add a.hbound b.hbound)) hb) h_exp
  bound := a.bound + b.bound
  hbound := by
    rw [ExactInt.sub_n]; exact le_trans (Int.natAbs_sub_le _ _) (Nat.add_le_add a.hbound b.hbound)

@[simp] theorem mul_bound (a b : ExactIntB R) (hb h_exp) :
    (a.mul b hb h_exp).bound = a.bound * b.bound := rfl
@[simp] theorem add_bound (a b : ExactIntB R) (hb h_exp) :
    (a.add b hb h_exp).bound = a.bound + b.bound := rfl
@[simp] theorem sub_bound (a b : ExactIntB R) (hb h_exp) :
    (a.sub b hb h_exp).bound = a.bound + b.bound := rfl

@[simp] theorem mul_n (a b : ExactIntB R) (hb h_exp) :
    (a.mul b hb h_exp).n = a.n * b.n := rfl
@[simp] theorem add_n (a b : ExactIntB R) (hb h_exp) :
    (a.add b hb h_exp).n = a.n + b.n := rfl
@[simp] theorem sub_n (a b : ExactIntB R) (hb h_exp) :
    (a.sub b hb h_exp).n = a.n - b.n := rfl

/-! ## The payoff: dot2 with a single representability hypothesis

Compare `ExactInt.dot2` (three separate `< 2^prec` bounds). Here the running bound lets one
hypothesis `bₐ₁·b_b₁ + bₐ₂·b_b₂ < 2^prec` discharge all three: each product bound is `≤` the
sum (summands nonneg), and the add's bound *is* the sum. -/
def dot2 (a₁ b₁ a₂ b₂ : ExactIntB R)
    (hb : a₁.bound * b₁.bound + a₂.bound * b₂.bound < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) : ExactIntB R :=
  (a₁.mul b₁ (lt_of_le_of_lt (Nat.le_add_right _ _) hb) h_exp).add
    (a₂.mul b₂ (lt_of_le_of_lt (Nat.le_add_left _ _) hb) h_exp) hb h_exp

/-- The reduction, by `rfl`: the bounded float dot product's integer value is the integer
dot product. -/
@[simp] theorem dot2_n (a₁ b₁ a₂ b₂ : ExactIntB R) (hb h_exp) :
    (dot2 a₁ b₁ a₂ b₂ hb h_exp).n = a₁.n * b₁.n + a₂.n * b₂.n := rfl

@[simp] theorem dot2_bound (a₁ b₁ a₂ b₂ : ExactIntB R) (hb h_exp) :
    (dot2 a₁ b₁ a₂ b₂ hb h_exp).bound = a₁.bound * b₁.bound + a₂.bound * b₂.bound := rfl

end ExactIntB
