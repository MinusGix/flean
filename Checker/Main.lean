import Flean.Checker.ModAddReadout

/-!
Executable entry point for the verified modadd readout checker.

Usage: `modadd_checker [weights.fleanten] [activations.fleanten] [--report-only | --rows N]`

Two passes over the 12769 input pairs:
1. an unverified *report* pass (per-row exact-rational margins, accuracy,
   progress), and
2. the verified pass: a single call to `checkReadout`, whose `true` result
   establishes `ReadoutCorrect` via `checkReadout_sound`.
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

def main (args : List String) : IO UInt32 := do
  let rowLimit : Option Nat := do
    let i ← args.idxOf? "--rows"
    (args.getD (i + 1) "").toNat?
  let rowsIdx := (args.idxOf? "--rows").getD args.length
  let pos := (args.zipIdx.filter fun (a, i) =>
    ¬a.startsWith "--" ∧ i ≠ rowsIdx + 1).map (·.1)
  let wPath := pos.getD 0 "references/large_files/modadd_weights.fleanten"
  let aPath := pos.getD 1 "references/large_files/modadd_activations.fleanten"
  let reportOnly := args.contains "--report-only"

  let weights ← readRawTensorFile wPath
  let acts ← readRawTensorFile aPath
  let some wU := RawTensor.find? weights "W_U" dModel vocab
    | throw (IO.userError "W_U (128 x 114) not found in weights file")
  let some resid := RawTensor.find? acts "resid" (p * p) dModel
    | throw (IO.userError "resid (12769 x 128) not found in activations file")

  -- Report pass: recompute logits per row, exact-rational margins.
  let nRows := min (rowLimit.getD (p * p)) (p * p)
  let mut correct := 0
  let mut minMargin : Option ℚ := none
  let t0 ← IO.monoMsNow
  for i in [0:nRows] do
    let a := i / p
    let b := i % p
    let lab := (a + b) % p
    let row := rowLogits resid.data wU.data i
    let vals : Array (Option ℚ) := row.map fpToRat?
    match vals.getD lab none with
    | none => IO.println s!"row {i} (a={a}, b={b}): label logit NON-FINITE"
    | some lv =>
      let mut worst : Option ℚ := none
      let mut ok := true
      for j in [0:vocab] do
        if j ≠ lab then
          match vals.getD j none with
          | none => ok := false
          | some v =>
            worst := some (max v (worst.getD v))
      match worst, ok with
      | some w, true =>
        let margin := lv - w
        if margin > 0 then correct := correct + 1
        else IO.println s!"row {i} (a={a}, b={b}): WRONG, margin {ratToString margin}"
        minMargin := some (min margin (minMargin.getD margin))
      | _, _ => IO.println s!"row {i}: non-finite wrong logit"
    if (i + 1) % 500 = 0 then
      let dt ← IO.monoMsNow
      IO.println s!"  … {i + 1}/{nRows} rows, {dt - t0} ms"
      (← IO.getStdout).flush
  let t1 ← IO.monoMsNow
  IO.println s!"report pass: {correct}/{nRows} rows correct ({t1 - t0} ms)"
  match minMargin with
  | some q => IO.println s!"min Binary32 logit margin (exact rational, truncated): {ratToString q 6}"
  | none => pure ()

  if reportOnly || rowLimit.isSome then
    return 0

  -- Verified pass: the compiled checker whose `true` is covered by
  -- `checkReadout_sound`.
  IO.println "verified pass: running checkReadout …"
  (← IO.getStdout).flush
  let t2 ← IO.monoMsNow
  let ok := checkReadout resid.data wU.data
  -- Print before reading the clock: forces `ok` (a pure binding the compiler
  -- may otherwise float past `IO.monoMsNow` into its first use).
  IO.println s!"checkReadout = {ok}"
  let t3 ← IO.monoMsNow
  IO.println s!"verified pass took {t3 - t2} ms"
  if ok then
    IO.println "⇒ ReadoutCorrect holds for these tensors (checkReadout_sound):"
    IO.println "  every pair (a,b): spec-Binary32 logit of (a+b) mod 113 strictly"
    IO.println "  exceeds all 113 other logits."
    return 0
  else
    IO.println "checker REJECTED the tensors"
    return 1
