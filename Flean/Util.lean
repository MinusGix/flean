import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Polyrith


namespace Int

theorem cast_natAbs_pos {R : Type*} [Ring R]
  {k : ℤ}
  : 0 < k → (k.natAbs : R) = (k : R) := by
  intro kpos
  rw [Nat.cast_natAbs, abs_of_pos kpos]

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

-- Connecting `zpow` and `pow` of a sort
theorem zpow_natAbs_nonneg_eq_zpow {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℤ} :
  0 < a → 0 ≤ n → (a ^ n.natAbs : R) = a ^ n := by
  intro ha hn
  induction n with
  | zero => simp
  | succ n ih =>
    have : 0 ≤ ↑n := by linarith
    have h1 := ih (by exact_mod_cast this)
    have h2 : ((n : ℤ) + 1).natAbs = (↑n : ℤ).natAbs + 1 := by aesop
    rw [h2]
    simp_all
    rw [pow_add, zpow_add_one₀]
    norm_num
    linarith
  | pred n ih =>
    have : 0 ≤ -(n : ℤ) := by linarith
    have h1 := ih (by exact_mod_cast this)
    have h2 : (-(n : ℤ) - 1).natAbs = (-(n : ℤ)).natAbs - 1 := by aesop
    rw [h2]
    simp_all

-- NOTE: Taken from mathlib since for some reason it is protected
theorem List.nodup_product {α : Type*} {β : Type*} {l₁ : List α} {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) : (l₁ ×ˢ l₂).Nodup :=
  List.nodup_flatMap.2
    ⟨fun a _ => d₂.map <| Function.LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases List.mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases List.mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

-- Doesn't exist in mathlib
@[simp]
theorem List.nodup_attachWith {α : Type*} {l : List α} (P : α → Prop) (H : ∀ x ∈ l, P x) : Nodup (attachWith l P H) ↔ Nodup l :=
  ⟨fun h => attachWith_map_subtype_val (p := P) (l := l) H ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attachWith_map_subtype_val (p := P) (l := l) H).symm ▸ h)⟩

theorem List.flatMap_singleton_cast_eq_map {α : Type*} {β : Type*} [c : Coe α β] (l : List α) : l.flatMap (fun x => [c.coe x]) = map (fun x => c.coe x) l := by
  unfold List.flatMap
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.flatten_cons, List.map_cons]
    rw [ih]
    simp

theorem List.flatMap_singleton_natCast_eq_map {l : List ℕ} : flatMap (fun x => [(x : ℤ)]) l = map (fun x => (x : ℤ)) l := by
  unfold List.flatMap
  induction l with
  | nil => simp
  | cons x xs ih => aesop

theorem List.pairwise_disjoint_range {n : ℕ} : List.Pairwise (fun a b => a ≠ b) (List.range n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ]
    simp
    rw [List.pairwise_append]
    split_ands
    · trivial
    · apply List.pairwise_singleton
    · intro a ain b bin
      rw [List.mem_singleton] at bin
      rw [bin]
      intro hn
      rw [hn] at ain
      exact List.not_mem_range_self ain
