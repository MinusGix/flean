import Flean.Checker.ModAddReadout

/-!
TEMPORARY benchmark (not part of the library): measures the cost of exact
alignment in `fpAddFinite` against a capped-shift + sticky-bit variant, on
significands drawn from the real checkpoint. Delete once the equivalence
theorem lands and the fast path is attached via `@[csimp]`.
-/

open Flean.Checker Flean.Checker.ModAdd

section Bench

variable [FloatFormat]
local notation "prec" => FloatFormat.prec

/-- Capped-alignment addition: shifts beyond `prec+3` are replaced by a sticky
bit, so every intermediate stays inside a machine word. -/
def fpAddFast [RModeExec] (a b : FiniteFp) : Fp :=
  let e_min := min a.e b.e
  let s : ℕ := (max a.e b.e - e_min - (FloatFormat.prec + 3)).toNat
  let shrink : ℕ → ℕ → ℕ := fun m e =>
    if e ≥ s then m <<< (e - s)
    else
      let d := s - e
      let q := m >>> d
      if q <<< d = m then q else q ||| 1
  let sa : ℤ := condNeg a.s (shrink a.m (a.e - e_min).toNat : ℤ)
  let sb : ℤ := condNeg b.s (shrink b.m (b.e - e_min).toNat : ℤ)
  let sum := sa + sb
  if sum = 0 then
    let result_sign : Bool := exactCancelSign a.s b.s
    Fp.finite ⟨result_sign, FloatFormat.min_exp, 0, IsValidFiniteVal.zero⟩
  else
    roundIntSigM (decide (sum < 0)) sum.natAbs (e_min - prec + 1 + s)

end Bench

attribute [local instance] instB32
local instance : UseRoundingPolicy RoundNearestEvenPolicy := ⟨⟩

/-- Fp-level wrapper mirroring `fpAdd`'s finite branch. -/
def fpAddFastFp (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | .infinite sx, .infinite sy => if sx = sy then .infinite sx else .NaN
  | .infinite s, .finite _ => .infinite s
  | .finite _, .infinite s => .infinite s
  | .finite a, .finite b => fpAddFast a b

/-- One dot product of length `n` over the given words, using `add`. -/
def dotWith (add : Fp → Fp → Fp) (xs ys : Array UInt32) (n : Nat) : Fp :=
  (List.range n).foldl
    (fun acc k => add acc (fpMul (decode (xs.getD k 0)) (decode (ys.getD k 0))))
    (decode 0)

def timeIt (label : String) (f : Unit → Fp) (reps : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut last := decode 0
  for _ in [0:reps] do
    last := f ()
  let dt := (← IO.monoMsNow) - t0
  IO.println s!"{label}: {dt} ms for {reps} reps (last = {(Fp.toRat? last).isSome})"

def main (args : List String) : IO UInt32 := do
  let wPath := args.getD 0 "references/large_files/modadd_weights.fleanten"
  let ts ← readRawTensorFile wPath
  let wU ← match RawTensor.find? ts "W_U" dModel vocab with
    | some t => pure t
    | none => throw (IO.userError "W_U not found")
  let xs := wU.data
  let ys := wU.data.reverse
  let reps := 400
  timeIt "exact-align fpAdd " (fun _ => dotWith fpAdd xs ys dModel) reps
  timeIt "capped+sticky fast" (fun _ => dotWith fpAddFastFp xs ys dModel) reps
  -- component isolation: decode only, decode+mul, decode+mul+add
  -- force decode: accumulate the significand so nothing can be eliminated
  let t0 ← IO.monoMsNow
  let mut sink := 0
  for _ in [0:reps] do
    sink := (List.range dModel).foldl
      (fun acc k => match decode (xs.getD k 0) with
        | .finite f => acc + f.m
        | _ => acc) sink
  IO.println s!"decode only       : {(← IO.monoMsNow) - t0} ms for {reps} reps (sink {sink % 7})"
  timeIt "decode+mul        "
    (fun _ => (List.range dModel).foldl
      (fun _ k => fpMul (decode (xs.getD k 0)) (decode (ys.getD k 0))) (decode 0)) reps
  timeIt "add only (acc+acc)"
    (fun _ => (List.range dModel).foldl (fun acc _ => fpAdd acc acc) (decode 0x3f800000)) reps
  -- predecoded: hoist decode out of the inner loop
  let xd := xs.map decode
  let yd := ys.map decode
  timeIt "predecoded dot    "
    (fun _ => (List.range dModel).foldl
      (fun acc k => fpAdd acc (fpMul (xd.getD k (decode 0)) (yd.getD k (decode 0))))
      (decode 0)) reps
  -- agreement check across many independent dot products
  let mut agree := 0
  let mut total := 0
  for off in [0:64] do
    let xs' := xs.extract (off * dModel) (off * dModel + dModel)
    let a := dotWith fpAdd xs' ys dModel
    let b := dotWith fpAddFastFp xs' ys dModel
    total := total + 1
    if a = b then agree := agree + 1
  IO.println s!"agreement: {agree}/{total} dot products bit-identical"
  return 0
