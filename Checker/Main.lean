import Flean.Checker.RawTensor

/-!
Executable entry point for the verified modadd checker. For now: read a
FLEANTEN file and report shapes, as a smoke test of the interchange layer.
-/

open Flean.Checker

def main (args : List String) : IO UInt32 := do
  let path := args.headD "references/large_files/modadd_weights.fleanten"
  let ts ← readRawTensorFile path
  let mut total := 0
  for t in ts do
    IO.println s!"{t.name}: {t.rows} x {t.cols}"
    total := total + t.rows * t.cols
  IO.println s!"total params: {total}"
  return 0
