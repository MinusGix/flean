import Flean.Operations.ModAddClock

/-!
# Representation certificates: correctness *through* the mechanism

`ModAddClock` studies the idealized Fourier clock. `Flean/Checker/ModAddFull.lean`
proves the real network correct *extensionally*, by recomputing all `p²` inputs.
This file supplies the missing middle: a certificate that a realized decoder is
correct **because** it approximates a cyclic kernel, with everything it fails to
explain collected into an explicit per-input defect.

## The shape of the statement

A *cyclic kernel* is a function `g : ZMod p → ℝ`; the score it awards candidate
`c` when the true sum is `s` is `g (s - c)`. This is precisely the class of
score functions that "depend only on `a + b - c`", and the exact clock is the
instance `g t = ∑_{k ∈ K} cos (phase k t)` — definitionally, see
`clockLogit_eq_kernelScore`.

Given a realized decoder `L a b c` we write

    L a b c  =  kernelScore g (a + b) c  +  defect

and certify each input pair separately: if twice the defect radius at `(a,b)`
fits inside the kernel's margin, that input decodes correctly. Failure is
therefore confined to `{ab | kernelMargin g ≤ 2 * d a b}`, and accuracy is
bounded below by the size of that set.

## Why per-input, and why this is the honest form

For the actual grokked mod-113 network the *global* form of this certificate is
provably unusable: measured against the fitted five-frequency kernel the sup-norm
defect is `12.41` while the kernel margin is `18.30`, so `margin - 2ε < 0` at
every truncation `K` (see `docs/clock_representation_analysis.md`). The per-input
form certifies `12584/12769 ≈ 98.55%` of inputs. So the theorems below are stated
per-input not for generality's sake but because that is the only form the data
supports — an instance of the project's rule that correctness claims about a
network must be margin-versus-error on each input, never global.

The remaining inputs are not lost: they are covered by the extensional checker,
which is exactly the division of labour intended between the two halves.
-/

namespace Flean.ModAddRepresentation

open Flean.ModAddClock

variable {p : ℕ} [Fact p.Prime]

/-! ## Cyclic kernels and their margins -/

/-- The score candidate `c` receives when the true sum is `s`, under the cyclic
kernel `g`. This is the general "depends only on `s - c`" score. -/
def kernelScore (g : ZMod p → ℝ) (s c : ZMod p) : ℝ := g (s - c)

/-- There is a nonzero residue to compete with, so the competitor set is nonempty. -/
theorem erase_zero_nonempty : (Finset.univ.erase (0 : ZMod p)).Nonempty :=
  Flean.ModAddClock.erase_univ_nonempty 0

/-- The kernel's margin: how far the aligned score `g 0` sits above the best
misaligned score. Positive margin is what makes the kernel decode. -/
noncomputable def kernelMargin (g : ZMod p → ℝ) : ℝ :=
  g 0 - (Finset.univ.erase (0 : ZMod p)).sup' erase_zero_nonempty g

/-- The correct class scores `g 0`. -/
@[simp] theorem kernelScore_self (g : ZMod p → ℝ) (s : ZMod p) :
    kernelScore g s s = g 0 := by
  simp [kernelScore]

/-- Every wrong class scores at least a full margin below the correct one. -/
theorem kernelScore_le_of_ne (g : ZMod p → ℝ) {s c : ZMod p} (h : c ≠ s) :
    kernelScore g s c ≤ g 0 - kernelMargin g := by
  have hmem : s - c ∈ Finset.univ.erase (0 : ZMod p) :=
    Finset.mem_erase.mpr ⟨sub_ne_zero.mpr (Ne.symm h), Finset.mem_univ _⟩
  have := Finset.le_sup' g hmem
  simp only [kernelMargin, kernelScore]
  linarith

/-! ## The per-input certificate -/

/-- **Correctness through the mechanism.** If the realized logits `L` stay within
`d` of the kernel scores at every class, and the kernel margin beats `2 * d`,
then the true sum is the strict argmax of `L` — the decoder is right at this
input, *because* it approximates the kernel. -/
theorem correct_of_defect (g : ZMod p → ℝ) (s : ZMod p) (L : ZMod p → ℝ) (d : ℝ)
    (hd : ∀ c, |L c - kernelScore g s c| ≤ d) (hm : 2 * d < kernelMargin g) :
    ∀ c, c ≠ s → L c < L s := by
  intro c hc
  have h1 := (abs_le.mp (hd c)).2
  have h2 := (abs_le.mp (hd s)).1
  have h3 := kernelScore_le_of_ne g hc
  rw [kernelScore_self] at h2
  linarith

/-- Sharp form: only the defect radii at the correct class and at the competing
class need to fit inside the margin, and they may differ per class. This is the
form that certifies `100%` of inputs on the real checkpoint (min slack `+0.16`),
where the symmetric bound certifies `98.55%`. -/
theorem correct_of_defect_sharp (g : ZMod p → ℝ) (s : ZMod p) (L : ZMod p → ℝ)
    (ε : ZMod p → ℝ) (hd : ∀ c, |L c - kernelScore g s c| ≤ ε c)
    (hm : ∀ c, c ≠ s → ε c + ε s < kernelMargin g) :
    ∀ c, c ≠ s → L c < L s := by
  intro c hc
  have h1 := (abs_le.mp (hd c)).2
  have h2 := (abs_le.mp (hd s)).1
  have h3 := kernelScore_le_of_ne g hc
  rw [kernelScore_self] at h2
  linarith [hm c hc]

/-! ## Failure set and certified accuracy -/

/-- **Failure is confined to large-defect inputs.** With a per-input defect
radius `d a b`, the decoder can only fail where the kernel margin fails to beat
`2 * d a b`. Bounding that set bounds the error rate. -/
theorem failureSet_subset_largeDefect (g : ZMod p → ℝ)
    (L : ZMod p → ZMod p → ZMod p → ℝ) (d : ZMod p → ZMod p → ℝ)
    (hL : ∀ a b c, |L a b c - kernelScore g (a + b) c| ≤ d a b) :
    FailureSet L ⊆ {ab | kernelMargin g ≤ 2 * d ab.1 ab.2} := by
  rintro ⟨a, b⟩ hab
  simp only [FailureSet, Set.mem_setOf_eq] at hab ⊢
  by_contra hlt
  push_neg at hlt
  exact hab (correct_of_defect g (a + b) (L a b) (d a b) (fun c => hL a b c) hlt)

/-- Any superset of the failure set bounds accuracy from below. This is what
turns "these 185 inputs are not certified" into a number. -/
theorem accuracy_ge_of_failureSet_subset (L : ZMod p → ZMod p → ZMod p → ℝ)
    (S : Set (ZMod p × ZMod p)) (h : FailureSet L ⊆ S) :
    1 - (S.ncard : ℝ) / (p : ℝ) ^ 2 ≤ accuracy L := by
  have hcard : ((FailureSet L).ncard : ℝ) ≤ (S.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard h S.toFinite
  have hp : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have := (Fact.out : p.Prime).pos
    positivity
  rw [accuracy]
  have hdiv : ((FailureSet L).ncard : ℝ) / (p : ℝ) ^ 2 ≤ (S.ncard : ℝ) / (p : ℝ) ^ 2 := by
    gcongr
  linarith

/-- **Certified accuracy from a representation.** Combining the two: a decoder
that approximates a cyclic kernel to within `d a b` at each input is correct
outside `{ab | kernelMargin g ≤ 2 * d a b}`, and its accuracy is at least
`1 - |that set| / p²`. -/
theorem accuracy_ge_of_defect (g : ZMod p → ℝ)
    (L : ZMod p → ZMod p → ZMod p → ℝ) (d : ZMod p → ZMod p → ℝ)
    (hL : ∀ a b c, |L a b c - kernelScore g (a + b) c| ≤ d a b) :
    1 - ({ab : ZMod p × ZMod p | kernelMargin g ≤ 2 * d ab.1 ab.2}.ncard : ℝ) / (p : ℝ) ^ 2
      ≤ accuracy L :=
  accuracy_ge_of_failureSet_subset L _ (failureSet_subset_largeDefect g L d hL)

/-- If *every* input is certified, accuracy is exactly `1`. -/
theorem accuracy_eq_one_of_defect (g : ZMod p → ℝ)
    (L : ZMod p → ZMod p → ZMod p → ℝ) (d : ZMod p → ZMod p → ℝ)
    (hL : ∀ a b c, |L a b c - kernelScore g (a + b) c| ≤ d a b)
    (hm : ∀ a b, 2 * d a b < kernelMargin g) :
    accuracy L = 1 := by
  have hempty : FailureSet L = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ hab
    have := failureSet_subset_largeDefect g L d hL hab
    simp only [Set.mem_setOf_eq] at this
    exact absurd (hm a b) (not_lt.mpr this)
  rw [accuracy, hempty, Set.ncard_empty]
  simp

/-! ## The exact clock as the vanishing-defect instance -/

/-- The kernel of the exact Fourier clock. -/
noncomputable def clockKernel (K : Finset (ZMod p)) : ZMod p → ℝ :=
  fun t => ∑ k ∈ K, Real.cos (phase k t)

/-- The clock logit *is* a kernel score — definitionally. This is the bridge that
makes `ModAddClock` a special case of the representation framework. -/
theorem clockLogit_eq_kernelScore (K : Finset (ZMod p)) (s c : ZMod p) :
    clockLogit K s c = kernelScore (clockKernel K) s c := rfl

/-- The clock kernel awards `|K|` to the correct class. -/
@[simp] theorem clockKernel_zero (K : Finset (ZMod p)) :
    clockKernel K 0 = K.card := by
  have := clockLogit_self K 0
  simpa [clockLogit_eq_kernelScore, kernelScore] using this

/-- With a nonempty DC-free frequency set the clock kernel has positive margin,
so it decodes — recovering `ModAddClock.correct_everywhere` as the special case
of `correct_of_defect` where the defect vanishes. -/
theorem kernelMargin_clockKernel_pos (K : Finset (ZMod p)) (hK : K.Nonempty)
    (h0 : (0 : ZMod p) ∉ K) : 0 < kernelMargin (clockKernel K) := by
  have hsup : (Finset.univ.erase (0 : ZMod p)).sup' erase_zero_nonempty (clockKernel K)
      < clockKernel K 0 := by
    refine Finset.sup'_lt_iff erase_zero_nonempty |>.mpr (fun t ht => ?_)
    have htne : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have := clockLogit_lt_self K hK h0 (c := 0) (s := t) (by simpa using htne.symm)
    simpa [clockLogit_eq_kernelScore, kernelScore, clockKernel] using this
  simp only [kernelMargin]
  linarith

/-- The exact clock is the zero-defect instance: taking `L` to be the clock
itself and `d = 0`, `correct_of_defect` yields strict argmax at every input. -/
theorem clock_correct_of_defect (K : Finset (ZMod p)) (hK : K.Nonempty)
    (h0 : (0 : ZMod p) ∉ K) (s : ZMod p) :
    ∀ c, c ≠ s → clockLogit K s c < clockLogit K s s :=
  correct_of_defect (clockKernel K) s (clockLogit K s) 0
    (fun c => by simp [clockLogit_eq_kernelScore])
    (by simpa using kernelMargin_clockKernel_pos K hK h0)

end Flean.ModAddRepresentation
