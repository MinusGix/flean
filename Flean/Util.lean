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

/-! ### Base-2 zpow simplification lemmas

These pre-discharge the `(2 : R) ≠ 0` obligation that `zpow_add₀`/`zpow_sub₀` require,
making zpow arithmetic with base 2 work with `simp`. -/

section ZpowTwo

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem two_zpow_mul (a b : ℤ) : (2 : R) ^ a * (2 : R) ^ b = (2 : R) ^ (a + b) :=
  (zpow_add₀ (by norm_num : (2 : R) ≠ 0) a b).symm

theorem two_zpow_div (a b : ℤ) : (2 : R) ^ a / (2 : R) ^ b = (2 : R) ^ (a - b) :=
  (zpow_sub₀ (by norm_num : (2 : R) ≠ 0) a b).symm

theorem mul_two_zpow_right (x : R) (a b : ℤ) :
    x * (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ (a + b) := by
  rw [mul_assoc, two_zpow_mul]

theorem div_two_zpow_mul_two_zpow (x : R) (a b : ℤ) :
    x / (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ (b - a) := by
  rw [div_mul_eq_mul_div, ← two_zpow_div, mul_div_assoc]

theorem mul_two_zpow_div_two_zpow (x : R) (a b : ℤ) :
    x * (2 : R) ^ a / (2 : R) ^ b = x * (2 : R) ^ (a - b) := by
  rw [mul_div_assoc, two_zpow_div]

theorem two_zpow_ne_zero (n : ℤ) : (2 : R) ^ n ≠ 0 :=
  zpow_ne_zero n (by norm_num : (2 : R) ≠ 0)

theorem two_zpow_pos' (n : ℤ) : (0 : R) < (2 : R) ^ n :=
  zpow_pos (by norm_num : (0 : R) < 2) n

theorem two_zpow_mono {a b : ℤ} (h : a ≤ b) : (2 : R) ^ a ≤ (2 : R) ^ b :=
  zpow_le_zpow_right₀ (by norm_num : (1 : R) ≤ 2) h

theorem two_zpow_strict_mono {a b : ℤ} (h : a < b) : (2 : R) ^ a < (2 : R) ^ b :=
  (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : R) < 2)).mpr h

end ZpowTwo

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

/-- `Int.log 2` of a scaled natural number: `Int.log 2 ((mag : R) * 2^e_base) = Nat.log2 mag + e_base`.
This bridges the `Nat.log2` used in `roundIntSigM` with the `Int.log 2` used in `findExponentDown`. -/
theorem int_log_nat_mul_zpow {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (mag : ℕ) (e_base : ℤ) (hmag : mag ≠ 0) :
    Int.log 2 ((mag : R) * (2 : R) ^ e_base) = (Nat.log2 mag : ℤ) + e_base := by
  have hmag_pos : (0 : R) < (mag : R) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmag)
  have hx_pos : (0 : R) < (mag : R) * (2 : R) ^ e_base :=
    mul_pos hmag_pos (zpow_pos (by norm_num : (0:R) < 2) _)
  -- Lower bound: 2^(Nat.log2 mag + e_base) ≤ mag * 2^e_base
  have hle : (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base) ≤ (mag : R) * (2 : R) ^ e_base := by
    rw [← two_zpow_mul, zpow_natCast]
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num : (0:R) ≤ 2) _)
    rw [← Nat.cast_ofNat, ← Nat.cast_pow]
    exact_mod_cast Nat.log2_self_le hmag
  -- Upper bound: mag * 2^e_base < 2^(Nat.log2 mag + e_base + 1)
  have hlt : (mag : R) * (2 : R) ^ e_base <
      (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base + 1) := by
    have hmag_lt_bits : (mag : R) < (2 : R) ^ ((Nat.log2 mag + 1 : ℕ) : ℤ) := by
      rw [zpow_natCast, ← Nat.cast_ofNat, ← Nat.cast_pow]
      exact_mod_cast @Nat.lt_log2_self mag
    calc (mag : R) * (2 : R) ^ e_base
        < (2 : R) ^ ((Nat.log2 mag + 1 : ℕ) : ℤ) * (2 : R) ^ e_base :=
          mul_lt_mul_of_pos_right hmag_lt_bits (zpow_pos (by norm_num) _)
      _ = (2 : R) ^ ((Nat.log2 mag : ℤ) + e_base + 1) := by
          rw [two_zpow_mul]; congr 1; push_cast; ring
  -- Conclude from characterization of Int.log
  have h1 : (Nat.log2 mag : ℤ) + e_base ≤ Int.log 2 ((mag : R) * (2 : R) ^ e_base) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hx_pos).mp hle
  have h2 : Int.log 2 ((mag : R) * (2 : R) ^ e_base) ≤ (Nat.log2 mag : ℤ) + e_base := by
    by_contra h
    push_neg at h
    have h' : (Nat.log2 mag : ℤ) + e_base + 1 ≤
        Int.log 2 ((mag : R) * (2 : R) ^ e_base) := by omega
    have hle' := (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hx_pos).mpr h'
    -- hle' : ↑2 ^ (...) ≤ mag * 2^e_base, but ↑2 = (2 : R)
    rw [show (↑(2 : ℕ) : R) = (2 : R) from by push_cast; ring] at hle'
    linarith
  omega

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
