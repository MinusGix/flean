import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The idealized "clock" algorithm for modular addition — with margins and a failure set

This is the first file of the **modular-addition transformer** thread: aim the reduction/abstract-
interpretation apparatus at a concrete, famous target — a 1-layer transformer trained to compute
`(a + b) mod p`, reverse-engineered (Nanda et al., *Progress measures for grokking*) to implement a
**Fourier "clock"**. Inputs are embedded as `(cos ωₖa, sin ωₖa)` on a set of frequencies `K`; trig
identities combine them into `cos ωₖ(a+b)`; the readout scores each candidate answer `c` by how well
`c` lines up with the recovered sum, and the argmax is `(a+b) mod p`.

This file formalizes the **idealized** algorithm (exact ℝ arithmetic, clean roots-of-unity phases),
which is "what we infer the network is computing." Later layers add (a) sparse/learned frequencies
and (b) floating-point, where the clean story *degrades* — and ML models do, in fact, fail on some
fraction of inputs. So the design principle, baked in here from the start, is:

> **Never state global correctness. State a per-input *margin*, and make correctness mean "margin
> beats the error."** The failure set is then `{inputs : margin ≤ error}`, and accuracy is
> `1 − |failure set| / p²`.

The headline objects:

* `clockLogit K s c` — the score class `c` receives when the true sum is `s`, using frequencies `K`.
* `clockLogit_lt_self` — with a nonempty, DC-free (`0 ∉ K`) frequency set, `s` is the **strict**
  argmax: every wrong class scores strictly lower. (A single frequency already suffices; this is the
  exact-arithmetic baseline, `margin > 0` everywhere — empty failure set.)
* `margin K s` — the gap between the correct score and the best competitor: the degradable quantity.
* `correct_under_perturbation` — **the failure criterion.** If a perturbed logit stays within `δ` of
  the ideal at every class and `2δ < margin`, decoding still returns `s`. Contrapositive: failure is
  confined to `{margin ≤ 2δ}`. This is the hook the floating-point correction will plug into (`δ` =
  the FP error), and the same `½`-style threshold as the discrete snapping bridge.

Why more frequencies help (the redundancy = error-correction story, proved in a later file): each
frequency is an independent estimate of the same answer, so `margin` grows with `|K|` while the FP
noise grows only like `√|K|` — the probabilistic √n law applied to the clock.
-/

namespace Flean.ModAddClock

open Real

variable {p : ℕ}

/-- The phase frequency `k` assigns to decoding offset `m`: `2π · (k·m) / p`, with `k·m` taken in
`ZMod p` (so the phase is canonically in `[0, 2π)`). At `m = 0` (correct alignment) the phase is `0`
and the cosine is `1`; this is the "hand of the clock pointing at 12". -/
noncomputable def phase (k m : ZMod p) : ℝ := 2 * π * ((k * m).val : ℝ) / p

/-- The idealized clock logit: the score candidate answer `c` receives when the true sum is `s`,
summing each frequency's alignment `cos(phase k (s − c))`. Maximal (`= |K|`) exactly when `c = s`. -/
noncomputable def clockLogit (K : Finset (ZMod p)) (s c : ZMod p) : ℝ :=
  ∑ k ∈ K, Real.cos (phase k (s - c))

/-- The correct answer scores the maximum possible, `|K|` (every frequency aligns perfectly). -/
theorem clockLogit_self (K : Finset (ZMod p)) (s : ZMod p) :
    clockLogit K s s = K.card := by
  have hone : ∀ k : ZMod p, Real.cos (phase k (s - s)) = 1 := by
    intro k; simp [phase, sub_self, mul_zero, ZMod.val_zero, Real.cos_zero]
  rw [clockLogit, Finset.sum_congr rfl (fun k _ => hone k), Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-- A single-frequency clock has just one term. -/
theorem clockLogit_singleton (k s c : ZMod p) :
    clockLogit {k} s c = Real.cos (phase k (s - c)) := by
  rw [clockLogit, Finset.sum_singleton]

variable [hp : Fact p.Prime]

/-- A nonzero frequency aligned with a nonzero offset gives a cosine strictly below `1`: the phase is
`2π·t/p` with `0 < t < p`, never a multiple of `2π`. (The single-hand version of "wrong answers
score lower".) -/
theorem cos_phase_lt_one {k m : ZMod p} (hk : k ≠ 0) (hm : m ≠ 0) :
    Real.cos (phase k m) < 1 := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hkm : k * m ≠ 0 := mul_ne_zero hk hm
  have hπ := Real.pi_pos
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have ht_pos : (0 : ℝ) < ((k * m).val : ℝ) := by exact_mod_cast ZMod.val_pos.mpr hkm
  have ht_lt : ((k * m).val : ℝ) < (p : ℝ) := by exact_mod_cast ZMod.val_lt (k * m)
  rcases (Real.cos_le_one (phase k m)).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [Real.cos_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hph : phase k m = (((k * m).val : ℝ) / p) * (2 * π) := by unfold phase; ring
    rw [hph] at hn
    have h2π : (2 * π) ≠ 0 := by positivity
    have hn' : (n : ℝ) = ((k * m).val : ℝ) / p := mul_right_cancel₀ h2π hn
    have hnp : (n : ℝ) * p = ((k * m).val : ℝ) := by rw [hn']; field_simp
    have hAR : (0 : ℝ) < n := by nlinarith [hnp, ht_pos, hp0]
    have hBR : (n : ℝ) < 1 := by nlinarith [hnp, ht_lt, hp0]
    have hA : 0 < n := by exact_mod_cast hAR
    have hB : n < 1 := by exact_mod_cast hBR
    omega

/-- **The strongest competitor is the adjacent class.** For a nonzero residue `r`, the cosine of its
phase is at most `cos(2π/p)` — the value at the residue closest to `0`. Cosine folds: `cos(2π·t/p)`
for `t ∈ {1,…,p−1}` is maximized at the ends `t = 1` and `t = p−1`. -/
theorem cos_two_pi_val_le {r : ZMod p} (hr : r ≠ 0) :
    Real.cos (2 * π * (r.val : ℝ) / p) ≤ Real.cos (2 * π / p) := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hπ := Real.pi_pos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have ht1 : 1 ≤ r.val := ZMod.val_pos.mpr hr
  have htlt : r.val < p := ZMod.val_lt r
  -- For `1 ≤ a` with `2a ≤ p` the angle is in `[2π/p, π]`, so cosine is antitone there.
  have key : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ p → Real.cos (2 * π * (a : ℝ) / p) ≤ Real.cos (2 * π / p) := by
    intro a ha1 ha2
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have ha2r : (2 * a : ℝ) ≤ p := by exact_mod_cast ha2
    refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
    · rw [div_le_iff₀ hpr]; nlinarith [mul_nonneg hπ.le (by linarith : (0 : ℝ) ≤ p - 2 * a)]
    · rw [show 2 * π * (a : ℝ) / p = (2 * π / p) * a from by ring]
      exact le_mul_of_one_le_right (by positivity) har
  rcases le_or_gt (2 * r.val) p with hcase | hcase
  · exact key r.val ht1 hcase
  · -- Fold `t` to `p − t`: `cos(2π t/p) = cos(2π(p−t)/p)`, and `p − t` lands in the first half.
    have huc : ((p - r.val : ℕ) : ℝ) = (p : ℝ) - r.val := by rw [Nat.cast_sub htlt.le]
    have hcast : 2 * π * (r.val : ℝ) / p = 2 * π - 2 * π * ((p - r.val : ℕ) : ℝ) / p := by
      rw [huc]; field_simp; ring
    rw [hcast, Real.cos_two_pi_sub]
    exact key (p - r.val) (by omega) (by omega)

/-- The phase cosine of any nonzero offset is at most `cos(2π/p)` — the single-frequency competitor
ceiling. Sharpens `cos_phase_lt_one`. -/
theorem cos_phase_le {k m : ZMod p} (hk : k ≠ 0) (hm : m ≠ 0) :
    Real.cos (phase k m) ≤ Real.cos (2 * π / p) := by
  simpa [phase] using cos_two_pi_val_le (mul_ne_zero hk hm)

/-- **Strict argmax (exact baseline).** With a nonempty, DC-free frequency set, every wrong answer
scores strictly below the correct one. This is `margin > 0` everywhere: in exact arithmetic the clock
never fails. -/
theorem clockLogit_lt_self (K : Finset (ZMod p)) (hK : K.Nonempty)
    (h0 : (0 : ZMod p) ∉ K) {s c : ZMod p} (hc : c ≠ s) :
    clockLogit K s c < clockLogit K s s := by
  rw [clockLogit_self]
  have hm : s - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  calc clockLogit K s c = ∑ k ∈ K, Real.cos (phase k (s - c)) := rfl
    _ < ∑ _k ∈ K, (1 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hK
          (fun k hk => cos_phase_lt_one (fun h => h0 (h ▸ hk)) hm)
    _ = K.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The decoder is **correct at sum `s`**: `s` strictly maximizes the clock logit, so any argmax
decoder returns `s = (a+b) mod p`. Phrased per-input so the failure set is just `{s | ¬ CorrectAt}`. -/
def CorrectAt (K : Finset (ZMod p)) (s : ZMod p) : Prop :=
  ∀ c, c ≠ s → clockLogit K s c < clockLogit K s s

/-- **Idealized accuracy = 100%.** With any nonempty DC-free frequency set, every sum decodes
correctly — the failure set is empty. This is the clean baseline the sparse-frequency and
floating-point layers will degrade into a genuine (bounded) failure set. -/
theorem correct_everywhere (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K) :
    ∀ s, CorrectAt K s := fun _ _ hc => clockLogit_lt_self K hK h0 hc

/-- The competitor set `{c | c ≠ s}` is nonempty (there are `p ≥ 2` classes), so the best-competitor
score is well defined. -/
theorem erase_univ_nonempty (s : ZMod p) : (Finset.univ.erase s).Nonempty := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  obtain ⟨t, ht⟩ := exists_ne s
  exact ⟨t, Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩⟩

/-- **The margin**: how much the correct score beats the best wrong score. The single degradable
quantity — every correctness statement downstream is "margin beats the error", and the failure set is
where it doesn't. -/
noncomputable def margin (K : Finset (ZMod p)) (s : ZMod p) : ℝ :=
  clockLogit K s s - (Finset.univ.erase s).sup' (erase_univ_nonempty s) (clockLogit K s)

/-- In the exact-arithmetic baseline the margin is strictly positive everywhere. -/
theorem margin_pos (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K) (s : ZMod p) :
    0 < margin K s := by
  rw [margin, sub_pos, Finset.sup'_lt_iff]
  exact fun c hc => clockLogit_lt_self K hK h0 (Finset.ne_of_mem_erase hc)

/-- **The failure criterion.** If an arbitrary perturbed logit `L` stays within `δ` of the ideal
clock logit at every class, and the margin exceeds `2δ`, then `s` is still the strict argmax of `L`,
so decoding still succeeds. Contrapositive: decoding can fail only where `margin ≤ 2δ` — *that* set,
of provably bounded size, is the failure set. With `L` the actual floating-point logit and `δ` its
forward-error bound, this is exactly how the FP layer will certify accuracy. -/
theorem correct_under_perturbation (K : Finset (ZMod p)) (s : ZMod p) (L : ZMod p → ℝ) (δ : ℝ)
    (hpert : ∀ c, |L c - clockLogit K s c| ≤ δ) (hmargin : 2 * δ < margin K s) :
    ∀ c, c ≠ s → L c < L s := by
  intro c hc
  have hcmem : c ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩
  have hsup : clockLogit K s c
      ≤ (Finset.univ.erase s).sup' (erase_univ_nonempty s) (clockLogit K s) :=
    Finset.le_sup' _ hcmem
  have hle : clockLogit K s c ≤ clockLogit K s s - margin K s := by rw [margin]; linarith
  have h1 := (abs_le.mp (hpert c)).2
  have h2 := (abs_le.mp (hpert s)).1
  linarith

/-! ## The decoder and accuracy

An argmax decoder reads off the predicted class as the highest-scoring `c`. The strict-argmax theorem
makes the prediction *the* modular sum, and lets us define the failure set / accuracy as first-class
objects: the idealized clock has an empty failure set (100% accuracy), and every later degradation
(sparse frequencies, floating point) is a (bounded) enlargement of that set. -/

/-- `c` is an argmax of the clock logits at sum `s` — a candidate output of any argmax decoder. -/
def IsArgmax (K : Finset (ZMod p)) (s c : ZMod p) : Prop :=
  ∀ c', clockLogit K s c' ≤ clockLogit K s c

/-- **The decoder computes modular addition.** With a nonempty DC-free frequency set, the argmax of
the clock logits at sum `s` is exactly `s`. So any argmax decoder returns `s` — and on inputs `a, b`
(`s = a + b`) that is `(a + b) mod p`. -/
theorem isArgmax_iff_eq (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K)
    {s c : ZMod p} : IsArgmax K s c ↔ c = s := by
  constructor
  · intro hc
    by_contra hne
    exact absurd (hc s) (not_le.mpr (clockLogit_lt_self K hK h0 hne))
  · rintro rfl c'
    rcases eq_or_ne c' c with h | h
    · exact le_of_eq (by rw [h])
    · exact (clockLogit_lt_self K hK h0 h).le

/-- The argmax decoder is well defined: a unique class maximizes the logits, namely `s`. -/
theorem existsUnique_argmax (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K)
    (s : ZMod p) : ∃! c, IsArgmax K s c :=
  ⟨s, (isArgmax_iff_eq K hK h0).mpr rfl, fun _ hc => (isArgmax_iff_eq K hK h0).mp hc⟩

/-- On inputs `a, b` the clock decodes to `a + b` in `ZMod p`: modular addition, recovered as the
argmax of the Fourier readout. -/
theorem clock_decodes_add (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K)
    (a b c : ZMod p) : IsArgmax K (a + b) c ↔ c = a + b :=
  isArgmax_iff_eq K hK h0

/-- The **failure set** of a (possibly floating-point) realized decoder whose logit for class `c` on
input `(a, b)` is `L a b c`: the input pairs where the true sum `a + b` is *not* the strict argmax.
This is the honest object for ML — correctness holds *on a set*, and `1 − |FailureSet| / p²` is the
certified accuracy. The idealized clock's failure set is empty; sparse frequencies and FP enlarge it,
and `correct_under_perturbation` confines the FP part to `{margin ≤ 2δ}`. -/
def FailureSet (L : ZMod p → ZMod p → ZMod p → ℝ) : Set (ZMod p × ZMod p) :=
  {ab | ¬ ∀ c, c ≠ ab.1 + ab.2 → L ab.1 ab.2 c < L ab.1 ab.2 (ab.1 + ab.2)}

/-- **Idealized accuracy is perfect.** The clock decoder (logits `clockLogit K (a+b) ·`) never fails:
its failure set is empty. -/
theorem failureSet_clock_eq_empty (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K) :
    FailureSet (fun a b c => clockLogit K (a + b) c) = ∅ := by
  ext ⟨a, b⟩
  simp only [FailureSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact fun c hc => clockLogit_lt_self K hK h0 hc

/-- Certified accuracy of a realized decoder: the fraction of the `p²` input pairs it gets right. -/
noncomputable def accuracy (L : ZMod p → ZMod p → ZMod p → ℝ) : ℝ :=
  1 - (FailureSet L).ncard / (p : ℝ) ^ 2

/-- The idealized clock decoder is `100%` accurate. This is the clean baseline that the sparse-
frequency and floating-point layers degrade into a `1 − ε` accuracy with `ε` an explicit bound on the
failure set. -/
theorem accuracy_clock_eq_one (K : Finset (ZMod p)) (hK : K.Nonempty) (h0 : (0 : ZMod p) ∉ K) :
    accuracy (fun a b c => clockLogit K (a + b) c) = 1 := by
  rw [accuracy, failureSet_clock_eq_empty K hK h0, Set.ncard_empty]
  simp

/-- **FP failure is confined to small-margin inputs.** If every realized logit `L a b c` — e.g. the
actual floating-point readout — stays within `δ` of the ideal clock logit, then the decoder fails
*only* where the clock margin is `≤ 2δ`. This is the certified-accuracy bridge: bound the small-margin
set and you bound the error rate. (`δ` will be the FP forward-error of the logit computation.) -/
theorem failureSet_subset_smallMargin (K : Finset (ZMod p))
    (L : ZMod p → ZMod p → ZMod p → ℝ) (δ : ℝ)
    (hL : ∀ a b c, |L a b c - clockLogit K (a + b) c| ≤ δ) :
    FailureSet L ⊆ {ab | margin K (ab.1 + ab.2) ≤ 2 * δ} := by
  rintro ⟨a, b⟩ hab
  simp only [FailureSet, Set.mem_setOf_eq] at hab ⊢
  by_contra hlt
  push_neg at hlt
  exact hab (correct_under_perturbation K (a + b) (L a b) δ (fun c => hL a b c) hlt)

/-- **Certified 100% accuracy under FP.** If the realized logits are within `δ` of the ideal and the
margin everywhere exceeds `2δ`, the floating-point decoder is *exactly* correct. The honest version
for a real model replaces "everywhere" by a bound on `{s | margin ≤ 2δ}`, giving `accuracy ≥ 1 − ε`
via `failureSet_subset_smallMargin`. -/
theorem accuracy_eq_one_of_margin_gt (K : Finset (ZMod p))
    (L : ZMod p → ZMod p → ZMod p → ℝ) (δ : ℝ)
    (hL : ∀ a b c, |L a b c - clockLogit K (a + b) c| ≤ δ) (hm : ∀ s, 2 * δ < margin K s) :
    accuracy L = 1 := by
  have hempty : FailureSet L = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ab hab
    have hsm := failureSet_subset_smallMargin K L δ hL hab
    simp only [Set.mem_setOf_eq] at hsm
    exact absurd (hm (ab.1 + ab.2)) (not_lt.mpr hsm)
  rw [accuracy, hempty, Set.ncard_empty]
  simp

/-! ## Single-frequency fragility — why redundancy is forced

A single frequency already decodes correctly in exact arithmetic (`clockLogit_lt_self`), but its
margin is *tiny*: exactly `1 − cos(2π/p)`, independent of the frequency and the input, and shrinking
like `2π²/p²`. So the floating-point tolerance of a one-frequency clock vanishes as `1/p²` — for large
`p` no fixed rounding error is survivable. This is the quantitative case for the Fourier redundancy
the trained network exhibits: only a *larger* margin (more frequencies) restores robustness. -/

/-- The adjacent class `s − k⁻¹` is the strongest competitor of `s`, scoring exactly `cos(2π/p)`. -/
theorem clockLogit_singleton_competitor {k : ZMod p} (hk : k ≠ 0) (s : ZMod p) :
    clockLogit {k} s (s - k⁻¹) = Real.cos (2 * π / p) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [clockLogit_singleton]
  congr 1
  rw [show s - (s - k⁻¹) = k⁻¹ from by ring, phase, mul_inv_cancel₀ hk, ZMod.val_one, Nat.cast_one,
    mul_one]

/-- **The single-frequency margin is `1 − cos(2π/p)`** — for every nonzero frequency `k` and every
input `s`. The strongest wrong answer (`s − k⁻¹`) hits `cos(2π/p)` and none beats it
(`cos_phase_le`), so the gap to the perfect score `1` is exactly `1 − cos(2π/p)`. -/
theorem margin_singleton {k : ZMod p} (hk : k ≠ 0) (s : ZMod p) :
    margin {k} s = 1 - Real.cos (2 * π / p) := by
  rw [margin, clockLogit_self, Finset.card_singleton, Nat.cast_one]
  congr 1
  refine le_antisymm (Finset.sup'_le _ _ (fun c hc => ?_)) ?_
  · rw [clockLogit_singleton]
    exact cos_phase_le hk (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hc)))
  · have hmem : (s - k⁻¹) ∈ Finset.univ.erase s :=
      Finset.mem_erase.mpr ⟨by rw [ne_eq, sub_eq_self]; exact inv_ne_zero hk, Finset.mem_univ _⟩
    calc Real.cos (2 * π / p) = clockLogit {k} s (s - k⁻¹) :=
          (clockLogit_singleton_competitor hk s).symm
      _ ≤ _ := Finset.le_sup' _ hmem

/-- **The `1/p²` fragility bound.** The single-frequency margin is at most `2π²/p²`, so it vanishes
quadratically in `p`. -/
theorem margin_singleton_le {k : ZMod p} (hk : k ≠ 0) (s : ZMod p) :
    margin {k} s ≤ 2 * π ^ 2 / p ^ 2 := by
  rw [margin_singleton hk]
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * π / (p : ℝ))
  have heq : (2 * π / p) ^ 2 / 2 = 2 * π ^ 2 / p ^ 2 := by rw [div_pow, mul_pow]; ring
  linarith [h, heq]

/-- **Single-frequency robustness threshold.** A one-frequency clock is *exactly* correct (`accuracy
= 1`) whenever the per-logit floating-point error stays below `(1 − cos(2π/p))/2 ≈ π²/p²`. Since that
tolerance shrinks like `1/p²`, a single frequency cannot survive a fixed rounding error at large `p`:
robustness *requires* the redundancy of multiple frequencies (a larger margin). -/
theorem singleton_accuracy_eq_one_of_lt {k : ZMod p} (hk : k ≠ 0)
    (L : ZMod p → ZMod p → ZMod p → ℝ) (δ : ℝ)
    (hL : ∀ a b c, |L a b c - clockLogit {k} (a + b) c| ≤ δ)
    (hδ : δ < (1 - Real.cos (2 * π / p)) / 2) :
    accuracy L = 1 := by
  refine accuracy_eq_one_of_margin_gt {k} L δ hL (fun s => ?_)
  rw [margin_singleton hk]; linarith

end Flean.ModAddClock
