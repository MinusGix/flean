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

/-- A positive rational equals `natAbs(num) / den` as a real. -/
theorem Rat.cast_eq_natAbs_div_den (r : ℚ) (hr : 0 < r) :
    (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
  have hnum : r.num = (r.num.natAbs : ℤ) :=
    (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hr))).symm
  have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    push_cast [Rat.cast_def]; ring
  rw [h1, show (r.num : ℝ) = (r.num.natAbs : ℝ) from by rw [hnum]; simp]

/-! ### Floor division bounds -/

/-- Nat floor division gives a lower bound in ℝ. -/
theorem nat_floor_div_mul_le (p d s : ℕ) :
    ((p * 2 ^ s / d : ℕ) : ℝ) * (d : ℝ) ≤ (p : ℝ) * 2 ^ s := by
  have := Nat.div_mul_le_self (p * 2 ^ s) d
  exact_mod_cast this

/-- Nat floor division gives a strict upper bound in ℝ. -/
theorem real_lt_nat_floor_div_succ_mul (p d s : ℕ) (hd : 0 < d) :
    (p : ℝ) * 2 ^ s < ((p * 2 ^ s / d + 1 : ℕ) : ℝ) * (d : ℝ) := by
  set a := p * 2 ^ s
  have h2 : a % d < d := Nat.mod_lt _ hd
  have h3 : d * (a / d) + a % d = a := Nat.div_add_mod a d
  have h4 : a < (a / d + 1) * d := by nlinarith
  exact_mod_cast h4

/-- `2 * x * 2^(-(s+1)) = x * 2^(-s)` for `s : ℤ`. -/
theorem two_mul_zpow_neg_succ (x : ℝ) (s : ℤ) :
    2 * x * (2 : ℝ) ^ (-s - 1) = x * (2 : ℝ) ^ (-s) := by
  rw [show -s - 1 = -s + (-1) from by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  ring

/-! ### Rational absolute value bound -/

theorem rat_abs_le_natAbs (x : ℚ) : |(x : ℝ)| ≤ (x.num.natAbs : ℝ) := by
  rw [show (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) from by
    exact_mod_cast (Rat.num_div_den x).symm, abs_div,
    abs_of_pos (show (0 : ℝ) < ↑x.den from by exact_mod_cast x.pos),
    show (x.num.natAbs : ℝ) = |(x.num : ℝ)| from by rw [Nat.cast_natAbs, Int.cast_abs]]
  exact div_le_self (abs_nonneg _) (by exact_mod_cast x.pos : (1 : ℝ) ≤ ↑x.den)

/-! ### Real.exp / Real.log utility lemmas -/

/-- `exp(k * log 2) = 2^k` for integer k. -/
theorem exp_int_mul_log2 (k : ℤ) :
    Real.exp (↑k * Real.log 2) = (2 : ℝ) ^ k := by
  rw [show (↑k : ℝ) * Real.log 2 = Real.log 2 * ↑k from by ring,
      Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.rpow_intCast]

/-- `exp(x) = 2^k * exp(x - k * log 2)` for integer k. -/
theorem exp_arg_red (x : ℝ) (k : ℤ) :
    Real.exp x = (2 : ℝ) ^ k * Real.exp (x - ↑k * Real.log 2) := by
  conv_lhs => rw [show x = ↑k * Real.log 2 + (x - ↑k * Real.log 2) from by ring]
  rw [Real.exp_add, exp_int_mul_log2]

theorem log2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp (1/2)).symm]
  exact Real.log_lt_log (Real.exp_pos _) (by
    have := Real.exp_bound' (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2 ≤ 1 by norm_num)
      (show 0 < 2 by omega)
    simp [Finset.sum_range_succ] at this; linarith)

theorem log2_lt_one : Real.log 2 < 1 := by
  calc Real.log 2 < Real.log (Real.exp 1) :=
        Real.log_lt_log (by norm_num) (by
          have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 3
          simp [Finset.sum_range_succ] at this; linarith)
    _ = 1 := Real.log_exp 1

theorem log2_lt_seven_eighths : Real.log 2 < 7 / 8 := by
  rw [show (7:ℝ)/8 = Real.log (Real.exp (7/8)) from (Real.log_exp (7/8)).symm]
  exact Real.log_lt_log (by norm_num) (by
    have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/8 by norm_num) 3
    simp [Finset.sum_range_succ] at this; linarith)

/-- MVT-type bound: `exp(b) - exp(a) ≤ exp(b) * (b - a)` for `a ≤ b`. -/
theorem exp_sub_le_mul_exp (a b : ℝ) :
    Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
  have h1 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    linarith [Real.add_one_le_exp (-(b - a))]
  have h2 : Real.exp b * (1 - (b - a)) ≤ Real.exp b * Real.exp (-(b - a)) :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_pos b).le
  have h3 : Real.exp b * Real.exp (-(b - a)) = Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  linarith

/-! ### Factorial / geometric decay bounds -/

/-- For `N ≥ 2 * m` and `d ≤ m`, the ratio `d^N / N!` is bounded by
`d^(2*m) / (2*m)! · (1/2)^(N - 2*m)`.
The idea: for `k > 2m ≥ 2d`, the factor `d/k ≤ d/(2m) ≤ 1/2`. -/
theorem pow_div_factorial_geometric_bound (d : ℝ) (hd : 0 ≤ d) (m : ℕ) (hm : d ≤ m)
    (N : ℕ) (hN : 2 * m ≤ N) :
    d ^ N / (N.factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ (N - 2 * m) := by
  -- Reduce to induction on j = N - 2m
  suffices h : ∀ j : ℕ, d ^ (2 * m + j) / ((2 * m + j).factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ j by
    have := h (N - 2 * m)
    rwa [Nat.add_sub_cancel' hN] at this
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    -- Factor: d^(2m+j+1)/(2m+j+1)! = (d^(2m+j)/(2m+j)!) · d/(2m+j+1)
    have hfac_ne : ((2 * m + j).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn1_pos : (0 : ℝ) < ((2 * m + j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio : d ^ (2 * m + j + 1) / ((2 * m + j + 1).factorial : ℝ) =
        (d ^ (2 * m + j) / ((2 * m + j).factorial : ℝ)) *
        (d / ((2 * m + j + 1 : ℕ) : ℝ)) := by
      rw [show 2 * m + j + 1 = (2 * m + j) + 1 from by omega,
          pow_succ, Nat.factorial_succ, Nat.cast_mul]
      field_simp
    -- Bound: d/(2m+j+1) ≤ 1/2 since d ≤ m and 2m+j+1 ≥ 2m+1 ≥ 2d
    have hfactor : d / ((2 * m + j + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn1_pos (by norm_num : (0:ℝ) < 2)]
      simp only [one_mul]
      calc d * 2 ≤ (m : ℝ) * 2 := by nlinarith
        _ = ((2 * m : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * m + j + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    -- Combine with inductive hypothesis
    rw [show 2 * m + (j + 1) = 2 * m + j + 1 from by omega, hratio]
    calc (d ^ (2 * m + j) / ↑(2 * m + j).factorial) *
            (d / ↑(2 * m + j + 1))
        ≤ (d ^ (2 * m) / ↑(2 * m).factorial * (1 / 2) ^ j) * (1 / 2) :=
          mul_le_mul ih hfactor (div_nonneg hd hn1_pos.le) (by positivity)
      _ = d ^ (2 * m) / ↑(2 * m).factorial * (1 / 2) ^ (j + 1) := by
          rw [pow_succ]; ring

/-- Explicit bound: `d^N / N! ≤ C · (1/2)^M` when `N = 2⌈d⌉ + M`. -/
theorem pow_div_factorial_effective (d : ℝ) (hd : 0 ≤ d) (M : ℕ) :
    let m := ⌈d⌉₊  -- Nat.ceil d
    let N := 2 * m + M
    d ^ N / (N.factorial : ℝ) ≤
      d ^ (2 * m) / ((2 * m).factorial : ℝ) * (1 / 2) ^ M := by
  simp only
  have hm : d ≤ ↑⌈d⌉₊ := Nat.le_ceil d
  have h := pow_div_factorial_geometric_bound d hd ⌈d⌉₊ hm (2 * ⌈d⌉₊ + M) (by omega)
  rwa [show 2 * ⌈d⌉₊ + M - 2 * ⌈d⌉₊ = M from by omega] at h
