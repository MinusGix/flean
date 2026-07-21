import Flean.Checker.ModAddReadout
import Flean.Operations.ModAddClock
import Mathlib.Tactic.NormNum.Prime

/-!
# Checker result in the accuracy framework

Bridges the executable readout checker to the kernel-pure accuracy vocabulary
of `ModAddClock`: if `ReadoutCorrect resid wU` holds (i.e. the compiled
`checkReadout` accepted the word arrays), then the realized real-valued logits
of the spec-Binary32 readout have **empty failure set** and **accuracy one**
in the sense of `Flean.ModAddClock.FailureSet`/`accuracy`.

`ReadoutCorrect` is slightly stronger than emptiness of the failure set: it
also dominates the 114th (`'='`) logit, which the `ZMod p`-indexed framework
does not see.
-/

namespace Flean.Checker.ModAdd

open Flean.ModAddClock

attribute [local instance] instB32

instance : Fact (Nat.Prime p) := ⟨by unfold p; norm_num⟩
instance : NeZero p := ⟨by unfold p; norm_num⟩

/-- The realized logit function of the spec-Binary32 readout, as a real-valued
decoder in the `ModAddClock` sense (junk value `0` at non-finite entries;
`ReadoutCorrect` guarantees finiteness wherever it matters). -/
noncomputable def realizedLogit (resid wU : Array UInt32) (a b c : ZMod p) : ℝ :=
  match specLogit resid wU (a.val * p + b.val) c.val with
  | .finite f => (f.toVal : ℝ)
  | _ => 0

/-- Equation lemma for `realizedLogit` at a finite spec logit. Rewrites the
match scrutinee syntactically; never reduces `specLogit` itself (whose
128-step fold must not be unfolded on symbolic arguments). -/
private theorem realizedLogit_of_finite (resid wU : Array UInt32)
    (a b c : ZMod p) (f : FiniteFp)
    (hf : specLogit resid wU (a.val * p + b.val) c.val = .finite f) :
    realizedLogit resid wU a b c = (f.toVal : ℝ) := by
  unfold realizedLogit
  rw [hf]

/-- A checker-accepted readout has empty failure set: on every input pair the
realized true-answer logit strictly exceeds every realized wrong-answer
logit. -/
theorem failureSet_realized_eq_empty (resid wU : Array UInt32)
    (h : ReadoutCorrect resid wU) :
    FailureSet (realizedLogit resid wU) = ∅ := by
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
  rw [realizedLogit_of_finite resid wU a b c fw hfw,
    realizedLogit_of_finite resid wU a b (a + b) ft hft]
  rw [← FiniteFp.toVal_ratCast fw, ← FiniteFp.toVal_ratCast ft]
  have hlt' : fw.toVal (R := ℚ) < ft.toVal (R := ℚ) := hlt
  exact_mod_cast hlt'

/-- **Checker-certified accuracy one.** If the compiled checker accepts the
tensors, the realized spec-Binary32 readout decodes `(a + b) mod 113` on all
`113²` input pairs. -/
theorem accuracy_realized_eq_one (resid wU : Array UInt32)
    (h : ReadoutCorrect resid wU) :
    accuracy (realizedLogit resid wU) = 1 := by
  rw [accuracy, failureSet_realized_eq_empty resid wU h, Set.ncard_empty]
  norm_num [p]

end Flean.Checker.ModAdd
