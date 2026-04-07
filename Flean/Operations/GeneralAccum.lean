import Flean.Operations.AffineFold
import Flean.Operations.Horner
import Flean.Operations.GeomBound

set_option maxHeartbeats 800000

/-!
# General Accumulator Error Bounds (Four-Parameter Model)

This file provides the four-parameter generalization of the accumulator error
framework from `AffineFoldInstances.lean`.

## The per-step model

Each accumulator step has separate error and growth rates for the accumulator
component vs the offset component:

- `|error_k| ≤ α_acc · κ · mag_k + α_off · offset_k`
- `mag_{k+1} ≤ (1 + β_acc) · κ · mag_k + (1 + β_off) · offset_k`

This captures the triangular 2D recurrence structure underlying all accumulator
error analysis (see `AccumulatorBounds.md`).

## Two independent proof paths

The file contains two inductive proofs that cannot be derived from each other:

1. **Four-parameter** (`weightedErrorSum_le_of_general_step`): two-term output,
   tight when α_acc ≠ α_off or β_acc ≠ β_off.

2. **Uniform** (`weightedErrorSum_le_of_uniform_step`): one-term output,
   tight when all four parameters are equal.

The four-parameter bound's offset coefficient can exceed `(1+α)^n - 1` in the
uniform case, so the max wrapper goes through the uniform path, not the
four-parameter path. This is not a limitation — it reflects that the two-term
decomposition into init + offset is not the same as the one-term polynomial form.

## Hierarchy

- `weightedErrorSum_le_of_general_step` — four-param, two-term output
- `weightedErrorSum_le_of_general_step_max` — four-param hypotheses → one-term output (via uniform)
- `weightedErrorSum_le_of_uniform_step` — uniform model (α_acc = α_off = β_acc = β_off = α)
-/

namespace GeneralAccum

open AffineFold Horner GeomBound

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Four-parameter model -/

/-- **General four-parameter weighted error sum bound** (two-term output).

The init term `geomBound(α_acc, β_acc, n) · κ^n · mag_0` tracks how the initial
accumulator magnitude generates error through n steps.

The offset term `(α_off + α_acc·(1+β_off)·geomBound(1, β_acc, n)) · hornerPoly(offsets, 0, κ)`
tracks direct offset error (α_off) plus offset-to-accumulator-to-error coupling.
The coupling uses a mild overcount: `geomBound(1, β_acc, n)` uniformly bounds the
position-dependent factor. -/
theorem weightedErrorSum_le_of_general_step
    (κ : R) (α_acc α_off β_acc β_off : R)
    (hκ : 0 ≤ κ) (hα_acc : 0 ≤ α_acc) (hα_off : 0 ≤ α_off)
    (hβ_acc : 0 ≤ β_acc) (hβ_off : 0 ≤ β_off)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α_acc * (κ * mags k) + α_off * offsets[k]'(by omega))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + β_acc) * (κ * mags k) + (1 + β_off) * offsets[k]'(by omega)) :
    weightedErrorSum κ errors ≤
      geomBound α_acc β_acc errors.length * κ ^ errors.length * mags 0 +
      (α_off + α_acc * (1 + β_off) * geomBound 1 β_acc errors.length) *
        hornerPoly offsets 0 κ := by
  induction errors generalizing offsets mags with
  | nil =>
    cases offsets with
    | nil => simp [weightedErrorSum, hornerPoly]
    | cons c cs => simp at hlen
  | cons e es ih =>
    match offsets, hlen with
    | [], hlen' => simp at hlen'
    | c :: cs, hlen' =>
      simp only [weightedErrorSum, List.length_cons, hornerPoly, zero_mul, zero_add]
      set n := es.length with hn
      set G := geomBound α_acc β_acc n with hG
      set O := geomBound 1 β_acc n with hO
      set A := α_off + α_acc * (1 + β_off) * O with hA
      have hlen_tail : es.length = cs.length := by simpa using hlen'
      have hcs_nn : ∀ c' ∈ cs, 0 ≤ c' := fun c' hc' =>
        hoffsets c' (List.mem_cons_of_mem _ hc')
      have ih_bound := ih cs (fun k => mags (k + 1)) hlen_tail hcs_nn
        (fun k => hmags_nn (k + 1))
        (fun k hk => herr (k + 1) (by simp; omega))
        (fun k hk => hrecur (k + 1) (by simp; omega))
      have hc_nn : (0 : R) ≤ c := hoffsets c (List.mem_cons.mpr (Or.inl rfl))
      have hκn : (0 : R) ≤ κ ^ n := pow_nonneg hκ n
      have hG_nn : (0 : R) ≤ G := hG ▸ geomBound_nonneg α_acc β_acc hα_acc hβ_acc n
      have hO_nn : (0 : R) ≤ O := hO ▸ geomBound_nonneg 1 β_acc (by positivity) hβ_acc n
      have hA_nn : (0 : R) ≤ A := hA ▸ by positivity
      have he : |e| ≤ α_acc * (κ * mags 0) + α_off * c := by
        simpa using herr 0 (by simp)
      have hm1 : mags 1 ≤ (1 + β_acc) * (κ * mags 0) + (1 + β_off) * c := by
        simpa using hrecur 0 (by simp)
      have htail_recur :
          G * κ ^ n * mags 1 ≤
            G * κ ^ n * ((1 + β_acc) * (κ * mags 0) + (1 + β_off) * c) :=
        mul_le_mul_of_nonneg_left hm1 (mul_nonneg hG_nn hκn)
      have hG_eq : G = α_acc * O := by
        rw [hG, hO]
        simpa using (geomBound_mul_left α_acc 1 β_acc n)
      have hgeom_succ : geomBound α_acc β_acc (n + 1) = α_acc + (1 + β_acc) * G := by
        rw [hG, geomBound_succ_eq]
      have hhorner_aff : hornerPoly cs c κ = hornerPoly cs 0 κ + c * κ ^ n := by
        have h := hornerPoly_affine cs 0 c κ
        rw [zero_add] at h
        rw [show cs.length = n from by rw [hn]; exact hlen_tail.symm] at h
        exact h
      have hO_le : O ≤ geomBound 1 β_acc (n + 1) :=
        hO ▸ geomBound_mono_n (by positivity) hβ_acc (Nat.le_succ n)
      have hA_le :
          A ≤ α_off + α_acc * (1 + β_off) * geomBound 1 β_acc (n + 1) := by
        rw [hA]
        have := mul_le_mul_of_nonneg_left hO_le (by positivity : (0:R) ≤ α_acc * (1 + β_off))
        linarith
      have hpoly_nn : (0 : R) ≤ hornerPoly cs c κ :=
        hornerPoly_nonneg cs c κ hc_nn hκ hcs_nn
      calc
        κ ^ n * |e| + weightedErrorSum κ es
            ≤ κ ^ n * (α_acc * (κ * mags 0) + α_off * c) +
                (G * κ ^ n * mags 1 + A * hornerPoly cs 0 κ) := by
              nlinarith [mul_le_mul_of_nonneg_left he hκn, ih_bound]
        _ ≤ κ ^ n * (α_acc * (κ * mags 0) + α_off * c) +
                (G * κ ^ n * ((1 + β_acc) * (κ * mags 0) + (1 + β_off) * c) +
                  A * hornerPoly cs 0 κ) := by
              linarith [htail_recur]
        _ = (α_acc + (1 + β_acc) * G) * κ ^ (n + 1) * mags 0 +
              A * hornerPoly cs c κ := by
              rw [pow_succ, hhorner_aff, hG_eq]; ring
        _ ≤ geomBound α_acc β_acc (n + 1) * κ ^ (n + 1) * mags 0 +
              (α_off + α_acc * (1 + β_off) * geomBound 1 β_acc (n + 1)) *
                hornerPoly cs c κ := by
              rw [hgeom_succ]
              linarith [mul_le_mul_of_nonneg_right hA_le hpoly_nn]

/-! ## Uniform model (independent proof path)

The uniform model `α_acc = α_off = β_acc = β_off = α` gives the tighter one-term
bound `((1+α)^n - 1) · hornerPoly(offsets, mag_0, κ)`. This cannot be derived
from the four-parameter theorem because the four-parameter offset coefficient
`α + α·(1+α)·geomBound(1, α, n)` can exceed `(1+α)^n - 1`. -/

/-- **Uniform accumulator error bound** (single α, one-term output).
    Matches `AffineFoldInstances.weightedErrorSum_le_of_relative_errors`. -/
theorem weightedErrorSum_le_of_uniform_step
    (κ α : R) (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α * (κ * mags k + offsets[k]'(by omega)))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + α) * (κ * mags k + offsets[k]'(by omega))) :
    weightedErrorSum κ errors ≤
      ((1 + α) ^ errors.length - 1) * hornerPoly offsets (mags 0) κ := by
  induction errors generalizing offsets mags with
  | nil =>
    cases offsets with
    | nil => simp [weightedErrorSum, hornerPoly]
    | cons c cs => simp at hlen
  | cons e es ih =>
    match offsets, hlen with
    | [], hlen' => simp at hlen'
    | c :: cs, hlen' =>
      simp only [weightedErrorSum, List.length_cons, hornerPoly]
      set n := es.length with hn
      set M := mags 0 * κ + c with hM
      set P := hornerPoly cs M κ with hP
      have hlen_tail : es.length = cs.length := by simpa using hlen'
      have hcs_nn : ∀ c' ∈ cs, 0 ≤ c' := fun c' hc' =>
        hoffsets c' (List.mem_cons_of_mem _ hc')
      have ih_bound := ih cs (fun k => mags (k + 1)) hlen_tail hcs_nn
        (fun k => hmags_nn (k + 1))
        (fun k hk => herr (k + 1) (by simp; omega))
        (fun k hk => hrecur (k + 1) (by simp; omega))
      have hMcomm : κ * mags 0 + c = M := by rw [hM, mul_comm]
      have he : |e| ≤ α * M := by rw [← hMcomm]; exact herr 0 (by simp)
      have hm1 : mags 1 ≤ (1 + α) * M := by rw [← hMcomm]; exact hrecur 0 (by simp)
      have hc_nn : (0 : R) ≤ c := hoffsets c (List.mem_cons.mpr (Or.inl rfl))
      have hM_nn : (0 : R) ≤ M := add_nonneg (mul_nonneg (hmags_nn 0) hκ) hc_nn
      have hκn : (0 : R) ≤ κ ^ n := pow_nonneg hκ n
      have h1α : (1 : R) ≤ 1 + α := by linarith
      have h1αn : (0 : R) ≤ (1 + α) ^ n := pow_nonneg (by linarith) n
      have h1αn_sub : (0 : R) ≤ (1 + α) ^ n - 1 := by linarith [one_le_pow₀ h1α (n := n)]
      have hP_mono : hornerPoly cs (mags 1) κ ≤ hornerPoly cs ((1 + α) * M) κ :=
        hornerPoly_mono cs _ _ κ hm1 hκ hcs_nn
      have hP_affine : hornerPoly cs ((1 + α) * M) κ = P + α * M * κ ^ n := by
        have h := hornerPoly_affine cs M (α * M) κ
        rw [show M + α * M = (1 + α) * M from by ring] at h
        rw [show cs.length = n from by rw [hn]; exact hlen_tail.symm] at h
        exact h
      have hMκn_le : M * κ ^ n ≤ P := by
        have hlen_cs : cs.length = n := by rw [hn]; exact hlen_tail.symm
        rw [hP, ← hlen_cs]
        exact hornerPoly_ge_acc_xpow cs M κ hκ hcs_nn
      have hP_nn : (0 : R) ≤ P := le_trans (mul_nonneg hM_nn hκn) hMκn_le
      have hpow_split : (1 + α) ^ (n + 1) - 1 =
          (1 + α) ^ n * α + ((1 + α) ^ n - 1) := by rw [pow_succ]; ring
      rw [hpow_split]
      nlinarith [mul_le_mul_of_nonneg_right he hκn,
                 mul_le_mul_of_nonneg_left (le_trans hP_mono (le_of_eq hP_affine)) h1αn_sub,
                 mul_le_mul_of_nonneg_left hMκn_le (mul_nonneg h1αn hα)]

/-! ## Max-parameter wrapper -/

/-- **Max-parameter collapse**: four-parameter hypotheses → one-term uniform output.

Derives uniform hypotheses from the four-parameter ones (since α_acc, α_off ≤ α and
β_acc, β_off ≤ α), then applies the uniform bound. This gives `((1+α)^n - 1) · P`
which is tighter than what the four-parameter theorem would produce when collapsed. -/
theorem weightedErrorSum_le_of_general_step_max
    (κ α : R) (α_acc α_off β_acc β_off : R)
    (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (hα_acc_le : α_acc ≤ α) (hα_off_le : α_off ≤ α)
    (hβ_acc_le : β_acc ≤ α) (hβ_off_le : β_off ≤ α)
    (_hα_acc : 0 ≤ α_acc) (_hα_off : 0 ≤ α_off)
    (_hβ_acc : 0 ≤ β_acc) (_hβ_off : 0 ≤ β_off)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α_acc * (κ * mags k) + α_off * offsets[k]'(by omega))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + β_acc) * (κ * mags k) + (1 + β_off) * offsets[k]'(by omega)) :
    weightedErrorSum κ errors ≤
      ((1 + α) ^ errors.length - 1) * hornerPoly offsets (mags 0) κ := by
  -- Derive uniform hypotheses from four-parameter ones
  have herr' : ∀ k (hk : k < errors.length),
      |errors[k]| ≤ α * (κ * mags k + offsets[k]'(by omega)) := by
    intro k hk
    have hk_err := herr k hk
    have hmag_nn : (0 : R) ≤ κ * mags k := mul_nonneg hκ (hmags_nn k)
    have hoff_nn : (0 : R) ≤ offsets[k]'(by omega) := hoffsets _ (List.getElem_mem _)
    calc |errors[k]|
        ≤ α_acc * (κ * mags k) + α_off * offsets[k]'(by omega) := hk_err
      _ ≤ α * (κ * mags k) + α * offsets[k]'(by omega) :=
          add_le_add (mul_le_mul_of_nonneg_right hα_acc_le hmag_nn)
                     (mul_le_mul_of_nonneg_right hα_off_le hoff_nn)
      _ = α * (κ * mags k + offsets[k]'(by omega)) := by ring
  have hrecur' : ∀ k (hk : k < errors.length),
      mags (k + 1) ≤ (1 + α) * (κ * mags k + offsets[k]'(by omega)) := by
    intro k hk
    have hk_rec := hrecur k hk
    have hmag_nn : (0 : R) ≤ κ * mags k := mul_nonneg hκ (hmags_nn k)
    have hoff_nn : (0 : R) ≤ offsets[k]'(by omega) := hoffsets _ (List.getElem_mem _)
    calc mags (k + 1)
        ≤ (1 + β_acc) * (κ * mags k) + (1 + β_off) * offsets[k]'(by omega) := hk_rec
      _ ≤ (1 + α) * (κ * mags k) + (1 + α) * offsets[k]'(by omega) :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) hmag_nn)
                     (mul_le_mul_of_nonneg_right (by linarith) hoff_nn)
      _ = (1 + α) * (κ * mags k + offsets[k]'(by omega)) := by ring
  exact weightedErrorSum_le_of_uniform_step κ α hκ hα errors offsets mags
    hlen hoffsets hmags_nn herr' hrecur'

/-! ## geomBound bridge for the uniform model

The uniform bound `((1+α)^n - 1) · P` is `geomBound α α n · P` by `geomBound_uniform`.
These restatements make the connection explicit. -/

/-- `weightedErrorSum_le_of_uniform_step` restated with `geomBound`. -/
theorem weightedErrorSum_le_of_uniform_step_geom
    (κ α : R) (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (errors offsets : List R) (mags : ℕ → R)
    (hlen : errors.length = offsets.length)
    (hoffsets : ∀ c ∈ offsets, 0 ≤ c)
    (hmags_nn : ∀ k, 0 ≤ mags k)
    (herr : ∀ k (hk : k < errors.length),
        |errors[k]| ≤ α * (κ * mags k + offsets[k]'(by omega)))
    (hrecur : ∀ k (hk : k < errors.length),
        mags (k + 1) ≤ (1 + α) * (κ * mags k + offsets[k]'(by omega))) :
    weightedErrorSum κ errors ≤
      geomBound α α errors.length * hornerPoly offsets (mags 0) κ := by
  rw [geomBound_uniform]
  exact weightedErrorSum_le_of_uniform_step κ α hκ hα errors offsets mags
    hlen hoffsets hmags_nn herr hrecur

/-! ## Composition theorem

When algorithm A's output feeds algorithm B's input, A's error becomes an
initial perturbation in B. The `geomBound_add` lemma provides the algebraic
core: `geomBound α β (m+n) = geomBound α β m · (1+β)^n + geomBound α β n`.

The composition theorem works at the abstract level: given bounds on A's and B's
weighted error sums, derive a bound on the composed error. -/

omit [IsStrictOrderedRing R] in
/-- **Weighted error sum splits over append.**

`weightedErrorSum κ (A ++ B) = κ^|B| · weightedErrorSum κ A + weightedErrorSum κ B`

This is the fundamental structural lemma for composition. -/
theorem weightedErrorSum_append (κ : R) (A B : List R) :
    weightedErrorSum κ (A ++ B) =
      κ ^ B.length * weightedErrorSum κ A + weightedErrorSum κ B := by
  induction A with
  | nil => simp [weightedErrorSum]
  | cons e es ih =>
    simp only [List.cons_append, weightedErrorSum, List.length_append]
    rw [ih, pow_add]
    ring

/-- **Composition via weighted error sum splitting.**

If `weightedErrorSum κ A ≤ bound_A` and `weightedErrorSum κ B ≤ bound_B`,
then `weightedErrorSum κ (A ++ B) ≤ κ^|B| · bound_A + bound_B`.

This is the general composition principle. Combined with `accumulator_error_bound`,
it chains two algorithms' error analyses. -/
theorem weightedErrorSum_compose'
    (κ : R) (hκ : 0 ≤ κ)
    (A B : List R)
    (bound_A bound_B : R)
    (hA : weightedErrorSum κ A ≤ bound_A)
    (hB : weightedErrorSum κ B ≤ bound_B) :
    weightedErrorSum κ (A ++ B) ≤
      κ ^ B.length * bound_A + bound_B := by
  rw [weightedErrorSum_append]
  have := mul_le_mul_of_nonneg_left hA (pow_nonneg hκ B.length)
  linarith

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Composition with `geomBound` closed form** (uniform model).

When both phases use the same parameters (α, κ), the composed bound
uses `geomBound_add`:
  `geomBound α α (m+n) · P = (geomBound α α m · (1+α)^n + geomBound α α n) · P`

This matches the intuition: A's error `geomBound α α m · P` is amplified by
`(1+α)^n` through B's growth, plus B's own `geomBound α α n · P`. -/
theorem geomBound_compose_uniform (α : R) (m n : ℕ) (P : R) :
    geomBound α α (m + n) * P =
      geomBound α α m * (1 + α) ^ n * P + geomBound α α n * P := by
  rw [geomBound_add]; ring

end GeneralAccum
