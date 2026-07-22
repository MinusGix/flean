import Flean.Checker.ModAddReadout
import Flean.IntegerEquivalence.ReluBits

/-!
# Verified MLP + readout checker for the grokked mod-113 network

Second rung of the verified-checker ladder (`docs/verified_checker_design.md`):
the trusted-activation boundary moves one layer up. Torch is now trusted only
for embeddings + attention (the exported post-attention residual `resid_mid`);
the **MLP** (`relu (W_in · x + b_in)`, then `x + W_out · h + b_out`) and the
**unembed** are re-executed inside Flean's Binary32 specification
(round-to-nearest-even, sequential left-to-right dot products, `Fp.fpRelu`).

Spec functions (`mlpHidden`, `mlpOut`, `mlpLogit`) are written as direct
mathematical definitions; the executable path (`rowLogitsMlp`,
`checkMlpReadout`) memoizes each stage in arrays and fans rows out across
`Task`s. Soundness (`checkMlpReadout_sound`) is parametric over all word
arrays; the `Task` layer is proof-transparent because `(Task.spawn f).get`
is definitionally `f ()`.

WARNING (proof code): never let `simp`/`whnf` reduce `seqDot`/`mlpHidden`/
`mlpOut`/`mlpLogit` applied to symbolic arguments — the folds over concrete
ranges (128/512 steps) explode. Rewrite match scrutinees and use
`seqDot_congr`/`getD_ofFn` instead.
-/

namespace Flean.Checker.ModAdd

attribute [local instance] instB32
local instance : UseRoundingPolicy RoundNearestEvenPolicy := ⟨⟩

/-- MLP hidden width. -/
def dMlp : ℕ := 512

/-- Sequential spec-Binary32 dot product of length `n`: one rounded multiply
and one rounded add per coordinate, left-to-right; non-finites propagate. -/
def seqDot (n : ℕ) (f g : ℕ → Fp) : Fp :=
  (List.range n).foldl (fun acc k => fpAdd acc (fpMul (f k) (g k))) (.finite 0)

/-- `seqDot` only reads its argument functions below `n`. -/
theorem seqDot_congr {n : ℕ} {f f' g g' : ℕ → Fp}
    (hf : ∀ k, k < n → f k = f' k) (hg : ∀ k, k < n → g k = g' k) :
    seqDot n f g = seqDot n f' g' := by
  unfold seqDot
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun k hk => hf k (by omega)) (fun k hk => hg k (by omega)),
      List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil,
      hf n (by omega), hg n (by omega)]

/-- `Array.getD` on `Array.ofFn` below the length. -/
theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (j : ℕ) (hj : j < n)
    (d : α) : (Array.ofFn f).getD j d = f ⟨j, hj⟩ := by
  have hsz : j < (Array.ofFn f).size := by simpa using hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
  simp

/-- `getD_ofFn` against an eta-clean `ℕ`-indexed function: avoids leaving
`f ⟨j, hj⟩` beta-redexes in goals. -/
theorem getD_ofFn' {α : Type*} {n : ℕ} {f : Fin n → α} {g : ℕ → α}
    (hfg : ∀ j : Fin n, f j = g j.val) (j : ℕ) (hj : j < n) (d : α) :
    (Array.ofFn f).getD j d = g j := by
  rw [getD_ofFn f j hj, hfg]

section Spec

variable (residMid wIn bIn wOut bOut wU : Array UInt32)

/-- Coordinate `k` of the (decoded) post-attention residual of row `i`. -/
def residAt (i k : ℕ) : Fp := decode (residMid.getD (i * dModel + k) 0)

/-- Hidden neuron `m` on row `i`: `relu (⟨W_in row m, x⟩ + b_in m)`,
all in spec Binary32. -/
def mlpHidden (i m : ℕ) : Fp :=
  Fp.fpRelu (fpAdd
    (seqDot dModel (residAt residMid i)
      (fun k => decode (wIn.getD (m * dModel + k) 0)))
    (decode (bIn.getD m 0)))

/-- Post-MLP residual coordinate `d` on row `i`:
`(x d + ⟨W_out row d, h⟩) + b_out d`. -/
def mlpOut (i d : ℕ) : Fp :=
  fpAdd (fpAdd (residAt residMid i d)
      (seqDot dMlp (fun m => decode (wOut.getD (d * dMlp + m) 0))
        (mlpHidden residMid wIn bIn i)))
    (decode (bOut.getD d 0))

/-- Logit `j` on row `i`: `⟨mlpOut row, W_U column j⟩`. -/
def mlpLogit (i j : ℕ) : Fp :=
  seqDot dModel (mlpOut residMid wIn bIn wOut bOut i)
    (fun k => decode (wU.getD (k * vocab + j) 0))

/-- The MLP+readout stack decodes modular addition: on every input pair the
true-answer logit is finite and strictly exceeds every other logit (exact
rational comparison of the decoded Binary32 values). -/
def MlpReadoutCorrect : Prop :=
  ∀ a, a < p → ∀ b, b < p → ∀ j, j < vocab → j ≠ (a + b) % p →
    ∃ ft fw : FiniteFp,
      mlpLogit residMid wIn bIn wOut bOut wU (a * p + b) ((a + b) % p)
        = .finite ft ∧
      mlpLogit residMid wIn bIn wOut bOut wU (a * p + b) j = .finite fw ∧
      fw.toRat < ft.toRat

end Spec

/-! ## Executable checker (memoized stages, row-parallel) -/

section Exec

variable (residMid wIn bIn wOut bOut wU : Array UInt32)

/-- One post-MLP coordinate computed against a memoized hidden array. -/
def outEntry (hidden : Array Fp) (i d : ℕ) : Fp :=
  fpAdd (fpAdd (residAt residMid i d)
      (seqDot dMlp (fun m => decode (wOut.getD (d * dMlp + m) 0))
        (fun m => hidden.getD m .NaN)))
    (decode (bOut.getD d 0))

/-- Memoized hidden layer of row `i`: each neuron computed exactly once. -/
def hiddenArr (i : ℕ) : Array Fp :=
  Array.ofFn (n := dMlp) fun m => mlpHidden residMid wIn bIn i m.val

/-- Memoized post-MLP residual of row `i`. -/
def outArr (i : ℕ) : Array Fp :=
  let hidden := hiddenArr residMid wIn bIn i
  Array.ofFn (n := dModel) fun d => outEntry residMid wOut bOut hidden i d.val

/-- One logit computed against a memoized post-MLP residual array. -/
def logitEntry (out : Array Fp) (j : ℕ) : Fp :=
  seqDot dModel (fun k => out.getD k .NaN)
    (fun k => decode (wU.getD (k * vocab + j) 0))

/-- All `vocab` logits of row `i`; each stage computed once. -/
def rowLogitsMlp (i : ℕ) : Array Fp :=
  let out := outArr residMid wIn bIn wOut bOut i
  Array.ofFn (n := vocab) fun j => logitEntry wU out j.val

/-- All rows of one outer index `a` (one `Task`'s worth of work). -/
def checkRowsForA (a : ℕ) : Bool :=
  (List.range p).all fun b =>
    checkRow (rowLogitsMlp residMid wIn bIn wOut bOut wU (a * p + b))
      ((a + b) % p)

/-- The checker: recompute and verify every row, fanned out per-`a` across
`Task`s. -/
def checkMlpReadout : Bool :=
  ((List.range p).map fun a => Task.spawn fun _ =>
      checkRowsForA residMid wIn bIn wOut bOut wU a).all
    fun t => t.get

end Exec

/-! ## Soundness -/

section Soundness

variable (residMid wIn bIn wOut bOut wU : Array UInt32)

private theorem hiddenArr_getD (i m : ℕ) (hm : m < dMlp) :
    (hiddenArr residMid wIn bIn i).getD m .NaN
      = mlpHidden residMid wIn bIn i m := by
  have hzeta : hiddenArr residMid wIn bIn i
      = Array.ofFn (n := dMlp) fun m => mlpHidden residMid wIn bIn i m.val :=
    rfl
  rw [hzeta, getD_ofFn' (g := mlpHidden residMid wIn bIn i) (fun _ => rfl) m hm]

private theorem outArr_getD (i d : ℕ) (hd : d < dModel) :
    (outArr residMid wIn bIn wOut bOut i).getD d .NaN
      = mlpOut residMid wIn bIn wOut bOut i d := by
  have hzeta : outArr residMid wIn bIn wOut bOut i
      = Array.ofFn (n := dModel) fun d =>
          outEntry residMid wOut bOut (hiddenArr residMid wIn bIn i) i d.val :=
    rfl
  have hs : seqDot dMlp (fun m => decode (wOut.getD (d * dMlp + m) 0))
      (fun m => (hiddenArr residMid wIn bIn i).getD m .NaN)
      = seqDot dMlp (fun m => decode (wOut.getD (d * dMlp + m) 0))
        (mlpHidden residMid wIn bIn i) :=
    seqDot_congr (fun k _ => rfl)
      (fun m hm => hiddenArr_getD residMid wIn bIn i m hm)
  rw [hzeta,
    getD_ofFn'
      (g := outEntry residMid wOut bOut (hiddenArr residMid wIn bIn i) i)
      (fun _ => rfl) d hd]
  unfold outEntry mlpOut
  rw [hs]

private theorem rowLogitsMlp_getD (i j : ℕ) (hj : j < vocab) :
    (rowLogitsMlp residMid wIn bIn wOut bOut wU i).getD j .NaN
      = mlpLogit residMid wIn bIn wOut bOut wU i j := by
  have hzeta : rowLogitsMlp residMid wIn bIn wOut bOut wU i
      = Array.ofFn (n := vocab) fun j =>
          logitEntry wU (outArr residMid wIn bIn wOut bOut i) j.val :=
    rfl
  rw [hzeta,
    getD_ofFn'
      (g := logitEntry wU (outArr residMid wIn bIn wOut bOut i))
      (fun _ => rfl) j hj]
  unfold logitEntry mlpLogit
  exact seqDot_congr
    (fun k hk => outArr_getD residMid wIn bIn wOut bOut i k hk)
    (fun k _ => rfl)

/-- Generic row soundness: `checkRow` accepting an array that pointwise agrees
with a logit function forces the strict-argmax property of that function. -/
theorem checkRow_sound' (row : Array Fp) (L : ℕ → Fp)
    (hrow : ∀ j, j < vocab → row.getD j .NaN = L j) (lab : ℕ)
    (hlab : lab < vocab) (h : checkRow row lab = true) :
    ∀ j, j < vocab → j ≠ lab →
      ∃ ft fw : FiniteFp,
        L lab = .finite ft ∧ L j = .finite fw ∧ fw.toRat < ft.toRat := by
  intro j hj hne
  unfold checkRow at h
  rw [hrow lab hlab] at h
  split at h
  case _ ft hft =>
    rw [List.all_eq_true] at h
    have hj' := h j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at hj'
    rcases hj' with hj' | hj'
    · exact absurd hj' hne
    · rw [hrow j hj] at hj'
      split at hj'
      case _ fw hfw =>
        exact ⟨ft, fw, hft, hfw, of_decide_eq_true hj'⟩
      case _ => exact absurd hj' (by simp)
  case _ => exact absurd h (by simp)

/-- `Task.spawn` is proof-transparent (definitional) when the body is a
variable; transporting a concrete body by defeq instead whnf-explodes. -/
theorem get_spawn_const {α : Type} (x : α) :
    (Task.spawn fun _ => x).get = x := rfl

/-- **Soundness**: if the compiled (row-parallel) checker accepts the word
arrays, the spec-Binary32 MLP + readout decodes modular addition —
parametric over all inputs. The `Task` fan-out is proof-transparent:
`(Task.spawn f).get` is definitionally `f ()`. -/
theorem checkMlpReadout_sound
    (h : checkMlpReadout residMid wIn bIn wOut bOut wU = true) :
    MlpReadoutCorrect residMid wIn bIn wOut bOut wU := by
  intro a ha b hb j hj hne
  unfold checkMlpReadout at h
  rw [List.all_eq_true] at h
  have htask : (Task.spawn fun _ =>
      checkRowsForA residMid wIn bIn wOut bOut wU a).get = true :=
    h _ (List.mem_map_of_mem (List.mem_range.mpr ha))
  rw [get_spawn_const] at htask
  unfold checkRowsForA at htask
  rw [List.all_eq_true] at htask
  have hrow := htask
  exact checkRow_sound'
    (rowLogitsMlp residMid wIn bIn wOut bOut wU (a * p + b))
    (mlpLogit residMid wIn bIn wOut bOut wU (a * p + b))
    (fun j hj => rowLogitsMlp_getD residMid wIn bIn wOut bOut wU (a * p + b) j hj)
    ((a + b) % p)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [p])) (by norm_num [p, vocab]))
    (hrow b (List.mem_range.mpr hb)) j hj hne

end Soundness

/-! ## Reporting helpers (no proof obligations) -/

/-- Margin of one logit row: label logit minus best wrong logit, exact in ℚ.
`none` if the label or any competitor logit is non-finite. -/
def rowMargin (row : Array Fp) (lab : ℕ) : Option ℚ := do
  let lv ← fpToRat? (row.getD lab .NaN)
  let mut worst : Option ℚ := none
  for j in [0:vocab] do
    if j ≠ lab then
      let v ← fpToRat? (row.getD j .NaN)
      worst := some (max v (worst.getD v))
  return lv - (← worst)

/-- Fold a row margin into a running (correct count, min margin). -/
def foldMargin (acc : Nat × Option ℚ) (m? : Option ℚ) : Nat × Option ℚ :=
  match m? with
  | none => acc
  | some m =>
    ((if m > 0 then acc.1 + 1 else acc.1), some (min m (acc.2.getD m)))

end Flean.Checker.ModAdd
