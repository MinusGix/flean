import Mathlib.Util.SynthesizeUsing
import Mathlib.Tactic.NormNum.Basic

import Flean.PowLinarith.Lemmas

open Lean Elab Tactic Meta Qq Mathlib

initialize registerTraceClass `pow_linarith

namespace PowLinarith

/-- A shorthand for getting the types of a list of proofs terms, to trace. -/
def powLinarithGetProofsMessage (l : List Expr) : MetaM MessageData := do
  return m!"{← l.mapM fun e => do instantiateMVars (← inferType e)}"


/--
A shorthand for tracing the types of a list of proof terms
when the `trace.linarith` option is set to true.
-/
def powLinarithTraceProofs {α} [ToMessageData α] (s : α) (l : List Expr) : MetaM Unit := do
  if ← isTracingEnabledFor `pow_linarith then
    addRawTrace <| .trace { cls := `pow_linarith } (toMessageData s) #[← powLinarithGetProofsMessage l]

end PowLinarith
