import Flean.Checker.ModAddReadout
import Flean.Checker.ModAddMlp

/-!
Executable entry point for the verified modadd checkers.

Usage:
  modadd_checker [weights.fleanten] [activations.fleanten]
                 [--layer mlp|readout] [--report-only] [--rows N]

`--layer readout` (first rung): trusts the torch pre-unembed residual,
recomputes the unembed in spec Binary32 (`checkReadout`/`checkReadout_sound`).
`--layer mlp` (default, second rung): trusts the torch post-attention
residual, recomputes MLP + unembed (`checkMlpReadout`/`checkMlpReadout_sound`).

Each mode runs an unverified *report* pass (exact-rational margins) and the
verified pass whose `true` is covered by the soundness theorem.
-/

open Flean.Checker Flean.Checker.ModAdd

/-- Fixed-point decimal rendering of an exact rational (truncated). -/
def ratToString (q : ℚ) (digits : ℕ := 4) : String :=
  let scale : ℤ := 10 ^ digits
  let n : ℤ := ⌊q * (scale : ℚ)⌋
  let sign := if n < 0 then "-" else ""
  let n := n.natAbs
  let frac := toString (n % scale.natAbs)
  let frac := "".pushn '0' (digits - frac.length) ++ frac
  s!"{sign}{n / scale.natAbs}.{frac}"

def reportSummary (nRows correct : Nat) (minMargin : Option ℚ) (ms : Nat) :
    IO Unit := do
  IO.println s!"report pass: {correct}/{nRows} rows correct ({ms} ms)"
  match minMargin with
  | some q =>
    IO.println s!"min Binary32 logit margin (exact rational, truncated): {ratToString q 6}"
  | none => IO.println "no finite margins"

def runReadout (resid wU : RawTensor) (rowLimit : Option Nat)
    (reportOnly : Bool) : IO UInt32 := do
  let nRows := min (rowLimit.getD (p * p)) (p * p)
  let mut correct := 0
  let mut minMargin : Option ℚ := none
  let t0 ← IO.monoMsNow
  for i in [0:nRows] do
    let row := rowLogits resid.data wU.data i
    let lab := (i / p + i % p) % p
    let m? := rowMargin row lab
    if m?.isNone ∨ m?.getD 0 ≤ 0 then
      IO.println s!"row {i} (a={i / p}, b={i % p}): WRONG or non-finite"
    (correct, minMargin) := foldMargin (correct, minMargin) m?
    if (i + 1) % 500 = 0 then
      IO.println s!"  … {i + 1}/{nRows} rows, {(← IO.monoMsNow) - t0} ms"
      (← IO.getStdout).flush
  reportSummary nRows correct minMargin ((← IO.monoMsNow) - t0)
  if reportOnly || rowLimit.isSome then
    return 0
  IO.println "verified pass: running checkReadout …"
  (← IO.getStdout).flush
  let t2 ← IO.monoMsNow
  let ok := checkReadout resid.data wU.data
  IO.println s!"checkReadout = {ok}"
  IO.println s!"verified pass took {(← IO.monoMsNow) - t2} ms"
  if ok then
    IO.println "⇒ ReadoutCorrect holds for these tensors (checkReadout_sound)."
    return 0
  else
    IO.println "checker REJECTED the tensors"
    return 1

def runMlp (residMid wIn bIn wOut bOut wU : RawTensor) (rowLimit : Option Nat)
    (reportOnly : Bool) : IO UInt32 := do
  let rowFor := fun (i : ℕ) =>
    rowLogitsMlp residMid.data wIn.data bIn.data wOut.data bOut.data wU.data i
  match rowLimit with
  | some n =>
    -- serial spot-check / timing mode
    let nRows := min n (p * p)
    let mut correct := 0
    let mut minMargin : Option ℚ := none
    let t0 ← IO.monoMsNow
    for i in [0:nRows] do
      let m? := rowMargin (rowFor i) ((i / p + i % p) % p)
      if m?.isNone ∨ m?.getD 0 ≤ 0 then
        IO.println s!"row {i} (a={i / p}, b={i % p}): WRONG or non-finite"
      (correct, minMargin) := foldMargin (correct, minMargin) m?
      IO.println s!"  row {i}: margin {(m?.map (ratToString · 6)).getD "none"}, {(← IO.monoMsNow) - t0} ms cumulative"
    reportSummary nRows correct minMargin ((← IO.monoMsNow) - t0)
    return 0
  | none =>
    -- parallel report pass, one task per outer index a
    let t0 ← IO.monoMsNow
    let tasks := (List.range p).map fun a => Task.spawn fun _ =>
      (List.range p).foldl (fun acc b =>
        foldMargin acc (rowMargin (rowFor (a * p + b)) ((a + b) % p)))
        ((0 : Nat), (none : Option ℚ))
    let mut correct := 0
    let mut minMargin : Option ℚ := none
    let mut done := 0
    for t in tasks do
      let (c, m?) := t.get
      correct := correct + c
      minMargin := match minMargin, m? with
        | some x, some y => some (min x y)
        | x, none => x
        | none, y => y
      done := done + 1
      if done % 16 = 0 then
        IO.println s!"  … {done}/{p} outer rows, {(← IO.monoMsNow) - t0} ms"
        (← IO.getStdout).flush
    reportSummary (p * p) correct minMargin ((← IO.monoMsNow) - t0)
    if reportOnly then
      return 0
    IO.println "verified pass: running checkMlpReadout …"
    (← IO.getStdout).flush
    let t2 ← IO.monoMsNow
    let ok := checkMlpReadout residMid.data wIn.data bIn.data wOut.data
      bOut.data wU.data
    IO.println s!"checkMlpReadout = {ok}"
    IO.println s!"verified pass took {(← IO.monoMsNow) - t2} ms"
    if ok then
      IO.println "⇒ MlpReadoutCorrect holds for these tensors (checkMlpReadout_sound):"
      IO.println "  from the post-attention residual, the spec-Binary32 MLP + unembed"
      IO.println "  puts (a+b) mod 113 strictly above all other logits, on every pair."
      return 0
    else
      IO.println "checker REJECTED the tensors"
      return 1

def main (args : List String) : IO UInt32 := do
  let valueOf (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let rowLimit : Option Nat := (valueOf "--rows").bind (·.toNat?)
  let layer := (valueOf "--layer").getD "mlp"
  let reportOnly := args.contains "--report-only"
  let flagVals := ["--rows", "--layer"].filterMap valueOf
  let pos := args.filter fun a => ¬a.startsWith "--" ∧ a ∉ flagVals
  let wPath := pos.getD 0 "references/large_files/modadd_weights.fleanten"
  let aPath := pos.getD 1 "references/large_files/modadd_activations.fleanten"

  let weights ← readRawTensorFile wPath
  let acts ← readRawTensorFile aPath
  let need (ts : Array RawTensor) (name : String) (r c : Nat) : IO RawTensor := do
    match RawTensor.find? ts name r c with
    | some t => return t
    | none => throw (IO.userError s!"{name} ({r} x {c}) not found")
  let wU ← need weights "W_U" dModel vocab

  match layer with
  | "readout" =>
    let resid ← need acts "resid" (p * p) dModel
    runReadout resid wU rowLimit reportOnly
  | "mlp" =>
    let residMid ← need acts "resid_mid" (p * p) dModel
    let wIn ← need weights "W_in" dMlp dModel
    let bIn ← need weights "b_in" 1 dMlp
    let wOut ← need weights "W_out" dModel dMlp
    let bOut ← need weights "b_out" 1 dModel
    runMlp residMid wIn bIn wOut bOut wU rowLimit reportOnly
  | l => throw (IO.userError s!"unknown --layer {l} (expected mlp|readout)")
