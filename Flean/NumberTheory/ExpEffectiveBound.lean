import Flean.NumberTheory.IrrationalExp
import Mathlib.Analysis.Complex.Exponential

/-! # Effective lower bound for `dist(exp(q)·2^s, ℤ)`

We prove that for nonzero rational `q = a/b` and any shift `s`,
the distance from `exp(q) · 2^s` to the nearest integer has a
computable positive lower bound.

The key idea is the **Taylor gap principle**: the Taylor partial sum
`S_N(q)` is rational, and after clearing denominators by `b^N · N!`,
we get an integer. The gap principle (`|J| ≥ 1` for nonzero `J ∈ ℤ`)
converts this into a lower bound on `|exp(q) · 2^s - m|`.

To ensure the integer `J` is nonzero, we use the fact that consecutive
partial sums `S_N(q) ≠ S_{N+1}(q)` (the next Taylor term is nonzero),
so for any target `m/2^s`, at most one can match.
-/

open Real

/-! ## Taylor partial sum -/

/-- The Taylor partial sum `S_N(x) = Σ_{k=0}^N x^k / k!` as a real number. -/
noncomputable def taylorPartialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ)

/-- Consecutive Taylor partial sums differ by `x^{N+1}/(N+1)!`. -/
theorem taylorPartialSum_succ (x : ℝ) (N : ℕ) :
    taylorPartialSum x (N + 1) = taylorPartialSum x N + x ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  simp [taylorPartialSum, Finset.sum_range_succ]

/-- For `x ≠ 0`, consecutive Taylor partial sums are distinct. -/
theorem taylorPartialSum_ne_succ (x : ℝ) (hx : x ≠ 0) (N : ℕ) :
    taylorPartialSum x N ≠ taylorPartialSum x (N + 1) := by
  rw [taylorPartialSum_succ]
  intro h
  have : x ^ (N + 1) / ((N + 1).factorial : ℝ) = 0 := by linarith
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h2
  · exact hx ((pow_eq_zero_iff (by omega : N + 1 ≠ 0)).mp h1)
  · exact absurd h2 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-! ## Clearing denominators -/

/-- `b^N · N! · S_N(a/b)` is an integer, proved by induction.
Base: `b^0 · 0! · S_0 = 1`.
Step: `b^{N+1} · (N+1)! · S_{N+1} = b · (N+1) · (b^N · N! · S_N) + a^{N+1}`. -/
theorem taylor_partial_sum_clears (a : ℤ) (b : ℕ) (hb : b ≠ 0) (N : ℕ) :
    ∃ A : ℤ, (b : ℝ) ^ N * (N.factorial : ℝ) *
      taylorPartialSum ((a : ℝ) / (b : ℝ)) N = (A : ℝ) := by
  induction N with
  | zero =>
    refine ⟨1, ?_⟩
    simp [taylorPartialSum, Finset.range_one]
  | succ N ih =>
    obtain ⟨A_N, hA_N⟩ := ih
    rw [taylorPartialSum_succ]
    -- b^{N+1} · (N+1)! · (S_N + a^{N+1}/b^{N+1}/(N+1)!)
    -- = b^{N+1} · (N+1)! · S_N + a^{N+1}
    have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hfac_ne : ((N + 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    -- The new term: b^{N+1} · (N+1)! · (a/b)^{N+1} / (N+1)! = a^{N+1}
    have hterm : (b : ℝ) ^ (N + 1) * ((N + 1).factorial : ℝ) *
        (((a : ℝ) / (b : ℝ)) ^ (N + 1) / ((N + 1).factorial : ℝ)) = (a : ℝ) ^ (N + 1) := by
      rw [div_pow]
      field_simp
    -- The old sum: b^{N+1} · (N+1)! · S_N = b · (N+1) · (b^N · N! · S_N)
    have hrecur : (b : ℝ) ^ (N + 1) * ((N + 1).factorial : ℝ) *
        taylorPartialSum ((a : ℝ) / (b : ℝ)) N =
        (b : ℝ) * ((N + 1 : ℕ) : ℝ) * ((b : ℝ) ^ N * (N.factorial : ℝ) *
          taylorPartialSum ((a : ℝ) / (b : ℝ)) N) := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
      ring
    refine ⟨(b : ℤ) * (N + 1 : ℤ) * A_N + a ^ (N + 1), ?_⟩
    rw [mul_add, hterm, hrecur, hA_N]
    push_cast; ring

/-! ## Key lemma: consecutive partial sums can't both match m/2^s -/

/-- For `q ≠ 0`, consecutive Taylor partial sums can't both equal the same
rational `m/2^s`, since they differ by a nonzero term. -/
theorem taylorPartialSum_not_both_eq (q : ℚ) (hq : q ≠ 0) (N s : ℕ) (m : ℤ) :
    taylorPartialSum (q : ℝ) N ≠ (m : ℝ) / 2 ^ s ∨
    taylorPartialSum (q : ℝ) (N + 1) ≠ (m : ℝ) / 2 ^ s := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have : taylorPartialSum (q : ℝ) N = taylorPartialSum (q : ℝ) (N + 1) := by
    rw [h1, h2]
  exact taylorPartialSum_ne_succ (q : ℝ) (by exact_mod_cast hq) N this

/-! ## The gap-to-distance lemma -/

/-- If `D > 0`, `D · v = J + ε` where `J ∈ ℤ \ {0}` and `|ε| ≤ 1/2`,
then `|v| ≥ 1/(2·D)`. -/
theorem abs_ge_of_int_gap {D v ε : ℝ} {J : ℤ} (hD : 0 < D)
    (hJ : J ≠ 0) (hε : |ε| ≤ 1 / 2) (hrel : D * v = (J : ℝ) + ε) :
    |v| ≥ 1 / (2 * D) := by
  have hJ_ge : (1 : ℝ) ≤ |(J : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hJ
  -- D * |v| = |D * v| = |J + ε| ≥ |J| - |ε| ≥ 1 - 1/2 = 1/2
  have h1 : D * |v| = |D * v| := by rw [abs_mul, abs_of_pos hD]
  rw [hrel] at h1
  have h2 : |(J : ℝ)| - |ε| ≤ |(J : ℝ) + ε| := by
    have : |(J : ℝ)| = |((J : ℝ) + ε) + (-ε)| := by ring_nf
    rw [this]
    linarith [abs_add_le ((J : ℝ) + ε) (-ε), abs_neg ε]
  have h3 : D * |v| ≥ 1 / 2 := by
    calc D * |v| = |(J : ℝ) + ε| := h1
    _ ≥ |(J : ℝ)| - |ε| := by linarith [h2]
    _ ≥ 1 - 1 / 2 := by linarith
    _ = 1 / 2 := by ring
  -- |v| ≥ 1/2 / D = 1/(2D)
  rw [ge_iff_le]
  have hv_pos : 0 ≤ |v| := abs_nonneg _
  have h4 : 1 / 2 ≤ D * |v| := h3
  -- 1/(2D) = (1/2) / D = (1/2) * (1/D)
  calc 1 / (2 * D) = 1 / 2 / D := by ring
    _ ≤ D * |v| / D := by exact div_le_div_of_nonneg_right h4 (le_of_lt hD)
    _ = |v| := by rw [mul_div_cancel_left₀ _ (ne_of_gt hD)]

/-! ## Floor locally constant -/

/-- If `v` is not an integer, then `⌊w⌋ = ⌊v⌋` for `w` sufficiently close to `v`. -/
theorem floor_eq_of_close {v w : ℝ}
    (hv : Int.fract v ≠ 0)
    (hw : |v - w| < min (Int.fract v) (1 - Int.fract v)) :
    ⌊w⌋ = ⌊v⌋ := by
  have hfrac_pos : 0 < Int.fract v := lt_of_le_of_ne (Int.fract_nonneg v) (Ne.symm hv)
  have hfrac_lt : Int.fract v < 1 := Int.fract_lt_one v
  have h1 : v - w < Int.fract v := by
    calc v - w ≤ |v - w| := le_abs_self _
    _ < min (Int.fract v) (1 - Int.fract v) := hw
    _ ≤ Int.fract v := min_le_left _ _
  have h2 : w - v < 1 - Int.fract v := by
    calc w - v ≤ |v - w| := by rw [abs_sub_comm]; exact le_abs_self _
    _ < min (Int.fract v) (1 - Int.fract v) := hw
    _ ≤ 1 - Int.fract v := min_le_right _ _
  have hv_decomp := Int.floor_add_fract v
  have hw_lower : (⌊v⌋ : ℝ) ≤ w := by linarith
  have hw_upper : w < (⌊v⌋ : ℝ) + 1 := by linarith
  exact Int.floor_eq_iff.mpr ⟨hw_lower, hw_upper⟩
