import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Polyrith


namespace Int

theorem cast_natAbs_pos {R : Type*} [Ring R]
  {k : ℤ}
  : 0 < k → (k.natAbs : R) = (k : R) := by
  intro kpos
  rw [Int.cast_natAbs, abs_of_pos kpos]

end Int

theorem Int.ceil_div_pos {R : Type*} [Field R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a b : R} :
  0 < a → 0 < b → 0 < ⌈a / b⌉ := by
  intro ha hb
  apply Int.ceil_pos.mpr
  apply div_pos ha hb

/-- If a ≥ 1, then ⌊a⌋ ≠ 0 -/
theorem Int.floor_ne_zero_ge_one {R : Type*} [Field R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R} :
  a ≥ 1 → ⌊a⌋ ≠ 0 := by
  intro ha hz
  have := Int.floor_eq_iff.mp hz
  norm_num at this
  linarith

theorem Int.floor_ne_zero_iff {R : Type*} [Field R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R} :
  ⌊a⌋ ≠ 0 ↔ 1 ≤ a ∨ a < 0 := by
  have hk := (Int.floor_eq_iff (R := R) (a := a) (z := 0)).not
  constructor
  · intro h
    have hk := hk.mp h
    rw [not_and_or] at hk
    norm_num at hk
    exact hk.symm
  · intro h
    apply hk.mpr
    intro h1
    norm_num at h1
    cases' h with h1 h2 <;> linarith

theorem Int.ceil_ne_zero_pos {R : Type*} [Field R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R} :
  0 < a → ⌈a⌉ ≠ 0 := by
  intro ha hz
  have := Int.ceil_eq_iff.mp hz
  norm_num at this
  linarith
