import Flean.Checker.ModAddReadout
import Flean.Checker.ModAddMlp
import Flean.Operations.ModAddClock
import Mathlib.Tactic.NormNum.Prime

/-!
# Checker results in the accuracy framework

Bridges the executable checkers to the kernel-pure accuracy vocabulary of
`ModAddClock`: a checker-accepted logit family (strict argmax at
`(a + b) % 113` in exact rational comparison) has **empty failure set** and
**accuracy one** in the sense of `Flean.ModAddClock.FailureSet`/`accuracy`.

The bridge is generic in the logit family `L : ℕ → ℕ → Fp`
(`ArgmaxCorrect`/`realizedOf`), then instantiated for the unembed-only
checker (`ReadoutCorrect`/`specLogit`) and the MLP + unembed checker
(`MlpReadoutCorrect`/`mlpLogit`).

The checker properties are slightly stronger than emptiness of the failure
set: they also dominate the 114th (`'='`) logit, which the `ZMod p`-indexed
framework does not see.
-/

namespace Flean.Checker.ModAdd

open Flean.ModAddClock

attribute [local instance] instB32

instance : Fact (Nat.Prime p) := ⟨by unfold p; norm_num⟩
instance : NeZero p := ⟨by unfold p; norm_num⟩

/-- The shared strict-argmax property of a logit family indexed by row
`i = a * p + b` and class `j`. -/
def ArgmaxCorrect (L : ℕ → ℕ → Fp) : Prop :=
  ∀ a, a < p → ∀ b, b < p → ∀ j, j < vocab → j ≠ (a + b) % p →
    ∃ ft fw : FiniteFp,
      L (a * p + b) ((a + b) % p) = .finite ft ∧
      L (a * p + b) j = .finite fw ∧
      fw.toRat < ft.toRat

theorem readoutCorrect_iff_argmax (resid wU : Array UInt32) :
    ReadoutCorrect resid wU ↔ ArgmaxCorrect (specLogit resid wU) := Iff.rfl

theorem mlpReadoutCorrect_iff_argmax
    (residMid wIn bIn wOut bOut wU : Array UInt32) :
    MlpReadoutCorrect residMid wIn bIn wOut bOut wU
      ↔ ArgmaxCorrect (mlpLogit residMid wIn bIn wOut bOut wU) := Iff.rfl

/-- The realized real-valued decoder of a logit family, in the `ModAddClock`
sense (junk value `0` at non-finite entries; `ArgmaxCorrect` guarantees
finiteness wherever it matters). -/
noncomputable def realizedOf (L : ℕ → ℕ → Fp) (a b c : ZMod p) : ℝ :=
  match L (a.val * p + b.val) c.val with
  | .finite f => (f.toVal : ℝ)
  | _ => 0

/-- Equation lemma for `realizedOf` at a finite logit. Rewrites the match
scrutinee syntactically; never reduces `L` itself (checker logit families
hide large folds that must not be unfolded on symbolic arguments). -/
private theorem realizedOf_of_finite (L : ℕ → ℕ → Fp) (a b c : ZMod p)
    (f : FiniteFp) (hf : L (a.val * p + b.val) c.val = .finite f) :
    realizedOf L a b c = (f.toVal : ℝ) := by
  unfold realizedOf
  rw [hf]

/-- A strict-argmax-correct logit family has empty failure set: on every input
pair the realized true-answer logit strictly exceeds every realized
wrong-answer logit. -/
theorem failureSet_realizedOf_eq_empty (L : ℕ → ℕ → Fp)
    (h : ArgmaxCorrect L) : FailureSet (realizedOf L) = ∅ := by
  ext ⟨a, b⟩
  simp only [FailureSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  intro c hc
  have hcval : c.val ≠ (a.val + b.val) % p := by
    intro heq
    apply hc
    have : c.val = (a + b).val := by rw [heq, ZMod.val_add]
    exact ZMod.val_injective p this
  obtain ⟨ft, fw, hft, hfw, hlt⟩ :=
    h a.val a.val_lt b.val b.val_lt c.val
      (lt_of_lt_of_le c.val_lt (by norm_num [p, vocab])) hcval
  rw [← ZMod.val_add a b] at hft
  rw [realizedOf_of_finite L a b c fw hfw,
    realizedOf_of_finite L a b (a + b) ft hft]
  rw [← FiniteFp.toVal_ratCast fw, ← FiniteFp.toVal_ratCast ft]
  have hlt' : fw.toVal (R := ℚ) < ft.toVal (R := ℚ) := hlt
  exact_mod_cast hlt'

/-- A strict-argmax-correct logit family decodes `(a + b) mod 113` on all
`113²` input pairs: accuracy one. -/
theorem accuracy_realizedOf_eq_one (L : ℕ → ℕ → Fp) (h : ArgmaxCorrect L) :
    accuracy (realizedOf L) = 1 := by
  rw [accuracy, failureSet_realizedOf_eq_empty L h, Set.ncard_empty]
  norm_num [p]

/-! ## Instantiations -/

/-- Realized logits of the unembed-only checker. -/
noncomputable def realizedLogit (resid wU : Array UInt32) : ZMod p → ZMod p → ZMod p → ℝ :=
  realizedOf (specLogit resid wU)

/-- Checker-accepted unembed readout ⟹ empty failure set. -/
theorem failureSet_realized_eq_empty (resid wU : Array UInt32)
    (h : ReadoutCorrect resid wU) :
    FailureSet (realizedLogit resid wU) = ∅ :=
  failureSet_realizedOf_eq_empty _ ((readoutCorrect_iff_argmax resid wU).mp h)

/-- **Checker-certified accuracy one** for the unembed readout. -/
theorem accuracy_realized_eq_one (resid wU : Array UInt32)
    (h : ReadoutCorrect resid wU) :
    accuracy (realizedLogit resid wU) = 1 :=
  accuracy_realizedOf_eq_one _ ((readoutCorrect_iff_argmax resid wU).mp h)

/-- Realized logits of the MLP + unembed checker. -/
noncomputable def realizedLogitMlp (residMid wIn bIn wOut bOut wU : Array UInt32) :
    ZMod p → ZMod p → ZMod p → ℝ :=
  realizedOf (mlpLogit residMid wIn bIn wOut bOut wU)

/-- Checker-accepted MLP + readout ⟹ empty failure set. -/
theorem failureSet_realizedMlp_eq_empty
    (residMid wIn bIn wOut bOut wU : Array UInt32)
    (h : MlpReadoutCorrect residMid wIn bIn wOut bOut wU) :
    FailureSet (realizedLogitMlp residMid wIn bIn wOut bOut wU) = ∅ :=
  failureSet_realizedOf_eq_empty _
    ((mlpReadoutCorrect_iff_argmax residMid wIn bIn wOut bOut wU).mp h)

/-- **Checker-certified accuracy one** for the spec-Binary32 MLP + readout. -/
theorem accuracy_realizedMlp_eq_one
    (residMid wIn bIn wOut bOut wU : Array UInt32)
    (h : MlpReadoutCorrect residMid wIn bIn wOut bOut wU) :
    accuracy (realizedLogitMlp residMid wIn bIn wOut bOut wU) = 1 :=
  accuracy_realizedOf_eq_one _
    ((mlpReadoutCorrect_iff_argmax residMid wIn bIn wOut bOut wU).mp h)

end Flean.Checker.ModAdd
