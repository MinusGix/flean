import Flean.Defs
import Flean.ToVal

/-!
# Tag definition: `HasAbsBound`

`HasAbsBound R c x` asserts `|(x.toVal : R)| ≤ c`.  Parametric over `R`
and over the bound `c`.  The third algebraic tag in the framework
(after `IsBoundedRange` and `IsNonneg`).

This file holds the structure definition plus basic structural lemmas
(`weaken`, `c_nonneg`, `neg`).  Propagation through FP ops lives in
`Flean/Tags/AbsBoundPropagate.lean` — the full sign-agnostic suite
`fp{Add,Sub,Mul,FMA}_{normal,unified}` plus the bridges to/from
`IsBoundedRange` and `isNormalRange`.

The earlier Phase 1 pilots `fpAdd_nonneg_normal` / `fpMul_nonneg_normal`
have been removed (T-S4 cleanup, 2026-04-27): they were superseded by
the sign-agnostic propagation theorems and had no callers outside this
file.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The tag -/

/-- `HasAbsBound R c x` asserts `|(x.toVal : R)| ≤ c`. Parametric over
`R` per design doc §1.8, parametric over the bound `c` to allow
per-value tagging. -/
structure HasAbsBound (c : R) (x : FiniteFp) : Prop where
  /-- `|x.toVal| ≤ c`. -/
  toVal_abs_le : |((x).toVal : R)| ≤ c

/-- **Vector-level** `HasAbsBound`: per-index magnitude tags packaged as
a single object.  Symmetric with the other vector-level tags
(`IsBoundedRange`, `IsSimplex`, `IsOneHot`).  Lets call sites pass
"per-index magnitude bounds" as one hypothesis rather than a `∀ i`. -/
structure HasAbsBoundVec {n : ℕ} (c : Fin n → R) (xs : Fin n → FiniteFp) : Prop where
  /-- Pointwise magnitude bound. -/
  pointwise : ∀ i, HasAbsBound (R := R) (c i) (xs i)

omit [IsStrictOrderedRing R] in
/-- Convenience projection: extract the scalar tag at index `i`. -/
theorem HasAbsBoundVec.at {n : ℕ} {c : Fin n → R} {xs : Fin n → FiniteFp}
    (h : HasAbsBoundVec (R := R) c xs) (i : Fin n) :
    HasAbsBound (R := R) (c i) (xs i) :=
  h.pointwise i

omit [IsStrictOrderedRing R] in
/-- Convenience projection: the raw inequality at index `i`. -/
theorem HasAbsBoundVec.toVal_abs_le {n : ℕ} {c : Fin n → R} {xs : Fin n → FiniteFp}
    (h : HasAbsBoundVec (R := R) c xs) (i : Fin n) :
    |((xs i).toVal : R)| ≤ c i :=
  (h.pointwise i).toVal_abs_le

/-! ## Basic properties -/

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Relaxing the bound preserves the tag. -/
theorem HasAbsBound.weaken {c c' : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) (hcc : c ≤ c') :
    HasAbsBound (R := R) c' x :=
  ⟨le_trans hx.toVal_abs_le hcc⟩

/-- The bound is automatically non-negative: `|x.toVal| ≤ c` implies `0 ≤ c`
since `0 ≤ |x.toVal|`.  Derivable; named for convenient forward use. -/
theorem HasAbsBound.c_nonneg {c : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) : (0 : R) ≤ c :=
  le_trans (abs_nonneg _) hx.toVal_abs_le

omit [IsStrictOrderedRing R] [FloorRing R] in
/-- Negation preserves the tag — `toVal` flips sign but magnitude is
invariant. No rounding, so no slack. -/
theorem HasAbsBound.neg {c : R} {x : FiniteFp}
    (hx : HasAbsBound (R := R) c x) :
    HasAbsBound (R := R) c (-x) := by
  refine ⟨?_⟩
  rw [FiniteFp.toVal_neg_eq_neg (R := R) x, abs_neg]
  exact hx.toVal_abs_le

end Flean.Tags
