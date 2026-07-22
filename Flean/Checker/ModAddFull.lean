import Flean.Checker.ModAddMlp
import Flean.Operations.Sub
import Flean.Operations.Div
import Flean.Operations.Exp
import Flean.Operations.ExpComputableDefs

/-!
# Verified full-forward-pass checker for the grokked mod-113 network

Final rung of the verified-checker ladder (`docs/verified_checker_design.md`):
**no torch activations remain**. The eleven raw weight tensors are the only
data; the entire forward pass — embedding + positional add, per-head
attention (QK scores, `1/√32` scaling, max-subtracted softmax via `fpExp` /
`fpDivFinite`, OV mix), residual adds, MLP with `Fp.fpRelu`, and unembed —
is executed inside Flean's Binary32 specification (round-to-nearest-even,
sequential left-to-right dot products).

Spec-fidelity notes (we fix *our* spec; we do not bit-match torch):
* the score scale is division by `sqrt32 = decode 0x40b504f3`, the Binary32
  nearest of `√32`, matching torch's `scores / np.sqrt(32)` up to summation
  order;
* the causal mask is irrelevant at the readout position (the `'='` token is
  last and attends to all three positions), so it does not appear;
* softmax subtracts the head's max score before `exp`, like torch.

`checkFullNet_sound` is parametric over all weight bundles. The executable
path memoizes each stage and fans rows out across `Task`s exactly as in
`ModAddMlp` (see the WARNING there about never whnf-ing the spec folds).
-/

namespace Flean.Checker.ModAdd

attribute [local instance] instB32
local instance : UseRoundingPolicy RoundNearestEvenPolicy := ⟨⟩

/-- Attention head width. -/
def dHead : ℕ := 32
/-- Number of attention heads. -/
def nHeads : ℕ := 4
/-- Context length (`[a, b, '=']`). -/
def nPos : ℕ := 3

/-- The eleven raw weight tensors of the p=113 architecture (word arrays in
the layouts fixed by `references/export_raw_tensors.py`). -/
structure Weights where
  wE : Array UInt32     -- (128, 114): row d, column token
  wPos : Array UInt32   -- (3, 128)
  wK : Array UInt32     -- (128, 128): row i*dHead+h
  wQ : Array UInt32     -- (128, 128)
  wV : Array UInt32     -- (128, 128)
  wO : Array UInt32     -- (128, 128): row d
  wIn : Array UInt32    -- (512, 128): row m
  bIn : Array UInt32    -- (1, 512)
  wOut : Array UInt32   -- (128, 512): row d
  bOut : Array UInt32   -- (1, 128)
  wU : Array UInt32     -- (128, 114): row d, column class

/-- NaN-propagating maximum of two `Fp`s (exact rational comparison). -/
def fpMax2 (x y : Fp) : Fp :=
  match x, y with
  | .finite fx, .finite fy =>
    if fx.toRat ≤ fy.toRat then .finite fy else .finite fx
  | _, _ => .NaN

/-- The Binary32 nearest of `√32` (word `0x40b504f3`), torch's score scale. -/
def sqrt32 : Fp := decode 0x40b504f3

/-! ## Specification: the forward pass as direct definitions -/

section Spec

variable (W : Weights) (a b : ℕ)

/-- Token at position `pos` of the input `[a, b, '=']` (`'=' = p`). -/
def tokenOf (pos : ℕ) : ℕ := if pos = 0 then a else if pos = 1 then b else p

/-- Embedding + positional: coordinate `d` of the layer input at `pos`. -/
def xEmb (pos d : ℕ) : Fp :=
  fpAdd (decode (W.wE.getD (d * vocab + tokenOf a b pos) 0))
    (decode (W.wPos.getD (pos * dModel + d) 0))

/-- Key coordinate: head-row `r = i * dHead + h`, position `pos`. -/
def kRow (r pos : ℕ) : Fp :=
  seqDot dModel (xEmb W a b pos) (fun d => decode (W.wK.getD (r * dModel + d) 0))

/-- Value coordinate. -/
def vRow (r pos : ℕ) : Fp :=
  seqDot dModel (xEmb W a b pos) (fun d => decode (W.wV.getD (r * dModel + d) 0))

/-- Query coordinate at the readout position (`pos = 2`). -/
def qRow (r : ℕ) : Fp :=
  seqDot dModel (xEmb W a b 2) (fun d => decode (W.wQ.getD (r * dModel + d) 0))

/-- Scaled attention score of head `i` against position `pos`. -/
def score (i pos : ℕ) : Fp :=
  fpDiv (seqDot dHead (fun h => kRow W a b (i * dHead + h) pos)
      (fun h => qRow W a b (i * dHead + h)))
    sqrt32

/-- Max score of head `i` (softmax stabilizer). -/
def smax (i : ℕ) : Fp :=
  fpMax2 (fpMax2 (score W a b i 0) (score W a b i 1)) (score W a b i 2)

/-- `exp (score − max)` of head `i`, position `pos`. -/
def expScore (i pos : ℕ) : Fp :=
  fpExp (fpSub (score W a b i pos) (smax W a b i))

/-- Softmax denominator of head `i`. -/
def denom (i : ℕ) : Fp :=
  fpAdd (fpAdd (expScore W a b i 0) (expScore W a b i 1)) (expScore W a b i 2)

/-- Attention weight of head `i` on position `pos`. -/
def attnW (i pos : ℕ) : Fp := fpDiv (expScore W a b i pos) (denom W a b i)

/-- Mixed value coordinate `r = i * dHead + h` at the readout position. -/
def zRow (r : ℕ) : Fp :=
  seqDot nPos (vRow W a b r) (attnW W a b (r / dHead))

/-- Attention output coordinate `d` (`W_O · z`). -/
def attnOutF (d : ℕ) : Fp :=
  seqDot dModel (zRow W a b) (fun f => decode (W.wO.getD (d * dModel + f) 0))

/-- Post-attention residual coordinate `d` at the readout position. -/
def residMidF (d : ℕ) : Fp := fpAdd (xEmb W a b 2 d) (attnOutF W a b d)

/-- Hidden neuron `m`: `relu (⟨W_in row m, x⟩ + b_in m)`. -/
def hiddenF (m : ℕ) : Fp :=
  Fp.fpRelu (fpAdd
    (seqDot dModel (residMidF W a b)
      (fun k => decode (W.wIn.getD (m * dModel + k) 0)))
    (decode (W.bIn.getD m 0)))

/-- Post-MLP residual coordinate `d`. -/
def outF (d : ℕ) : Fp :=
  fpAdd (fpAdd (residMidF W a b d)
      (seqDot dMlp (fun m => decode (W.wOut.getD (d * dMlp + m) 0))
        (hiddenF W a b)))
    (decode (W.bOut.getD d 0))

/-- Logit of class `j` on input `(a, b)`: the complete forward pass. -/
def fullLogit (j : ℕ) : Fp :=
  seqDot dModel (outF W a b) (fun k => decode (W.wU.getD (k * vocab + j) 0))

/-- **The network computes modular addition**: on every input pair, the
spec-Binary32 forward pass from raw weights puts `(a + b) % p` strictly
above every other logit (exact rational comparison). -/
def FullNetCorrect : Prop :=
  ∀ a, a < p → ∀ b, b < p → ∀ j, j < vocab → j ≠ (a + b) % p →
    ∃ ft fw : FiniteFp,
      fullLogit W a b ((a + b) % p) = .finite ft ∧
      fullLogit W a b j = .finite fw ∧
      fw.toRat < ft.toRat

end Spec

/-! ## Executable checker (memoized stages, row-parallel) -/

section Exec

variable (W : Weights) (a b : ℕ)

/-- Memoized query vector. -/
def qArrD : Array Fp := Array.ofFn (n := dModel) fun r => qRow W a b r.val

/-- One scaled score against a memoized query; flat index `e = i * nPos + pos`. -/
def scoreEntry (qA : Array Fp) (e : ℕ) : Fp :=
  fpDiv (seqDot dHead
      (fun h => kRow W a b ((e / nPos) * dHead + h) (e % nPos))
      (fun h => qA.getD ((e / nPos) * dHead + h) .NaN))
    sqrt32

/-- Memoized scaled scores (`nHeads * nPos` entries). -/
def scoreArrD : Array Fp :=
  let qA := qArrD W a b
  Array.ofFn (n := nHeads * nPos) fun e => scoreEntry W a b qA e.val

/-- One stabilized exponential against memoized scores. -/
def expEntry (sA : Array Fp) (e : ℕ) : Fp :=
  fpExp (fpSub (sA.getD e .NaN)
    (fpMax2 (fpMax2 (sA.getD (e / nPos * nPos) .NaN)
        (sA.getD (e / nPos * nPos + 1) .NaN))
      (sA.getD (e / nPos * nPos + 2) .NaN)))

/-- Memoized stabilized exponentials. -/
def expArrD : Array Fp :=
  let sA := scoreArrD W a b
  Array.ofFn (n := nHeads * nPos) fun e => expEntry sA e.val

/-- One attention weight against memoized exponentials. -/
def attnEntry (eA : Array Fp) (e : ℕ) : Fp :=
  fpDiv (eA.getD e .NaN)
    (fpAdd (fpAdd (eA.getD (e / nPos * nPos) .NaN)
        (eA.getD (e / nPos * nPos + 1) .NaN))
      (eA.getD (e / nPos * nPos + 2) .NaN))

/-- Memoized attention weights. -/
def attnArrD : Array Fp :=
  let eA := expArrD W a b
  Array.ofFn (n := nHeads * nPos) fun e => attnEntry eA e.val

/-- One mixed value coordinate against memoized attention weights. -/
def zEntry (atA : Array Fp) (r : ℕ) : Fp :=
  seqDot nPos (vRow W a b r)
    (fun pos => atA.getD (r / dHead * nPos + pos) .NaN)

/-- Memoized mixed values. -/
def zArrD : Array Fp :=
  let atA := attnArrD W a b
  Array.ofFn (n := dModel) fun r => zEntry W a b atA r.val

/-- One post-attention residual coordinate against memoized mixed values. -/
def midEntry (zA : Array Fp) (d : ℕ) : Fp :=
  fpAdd (xEmb W a b 2 d)
    (seqDot dModel (fun f => zA.getD f .NaN)
      (fun f => decode (W.wO.getD (d * dModel + f) 0)))

/-- Memoized post-attention residual. -/
def midArrD : Array Fp :=
  let zA := zArrD W a b
  Array.ofFn (n := dModel) fun d => midEntry W a b zA d.val

/-- One hidden neuron against a memoized residual. -/
def hidEntry (midA : Array Fp) (m : ℕ) : Fp :=
  Fp.fpRelu (fpAdd
    (seqDot dModel (fun k => midA.getD k .NaN)
      (fun k => decode (W.wIn.getD (m * dModel + k) 0)))
    (decode (W.bIn.getD m 0)))

/-- One post-MLP coordinate against memoized residual and hidden arrays. -/
def outEntryF (midA hidA : Array Fp) (d : ℕ) : Fp :=
  fpAdd (fpAdd (midA.getD d .NaN)
      (seqDot dMlp (fun m => decode (W.wOut.getD (d * dMlp + m) 0))
        (fun m => hidA.getD m .NaN)))
    (decode (W.bOut.getD d 0))

/-- One logit against a memoized post-MLP residual. -/
def logitEntryF (outA : Array Fp) (j : ℕ) : Fp :=
  seqDot dModel (fun k => outA.getD k .NaN)
    (fun k => decode (W.wU.getD (k * vocab + j) 0))

/-- All `vocab` logits of input `(a, b)`; every stage computed once. -/
def rowLogitsFull : Array Fp :=
  let midA := midArrD W a b
  let hidA := Array.ofFn (n := dMlp) fun m => hidEntry W midA m.val
  let outA := Array.ofFn (n := dModel) fun d => outEntryF W midA hidA d.val
  Array.ofFn (n := vocab) fun j => logitEntryF W outA j.val

/-- All rows of one outer index `a` (one `Task`'s worth of work). -/
def checkRowsForAFull (a : ℕ) : Bool :=
  (List.range p).all fun b =>
    checkRow (rowLogitsFull W a b) ((a + b) % p)

/-- The checker: the complete forward pass from raw weights, verified on
every input pair, fanned out per-`a` across `Task`s. -/
def checkFullNet : Bool :=
  ((List.range p).map fun a => Task.spawn fun _ =>
      checkRowsForAFull W a).all
    fun t => t.get

end Exec

/-! ## Soundness -/

section Soundness

variable (W : Weights) (a b : ℕ)

private theorem nPos_eq : nPos = 3 := rfl
private theorem dHead_eq : dHead = 32 := rfl
private theorem nHeads_eq : nHeads = 4 := rfl
private theorem dModel_eq : dModel = 128 := rfl
private theorem dMlp_eq : dMlp = 512 := rfl

private theorem qArrD_getD (r : ℕ) (hr : r < dModel) :
    (qArrD W a b).getD r .NaN = qRow W a b r := by
  have hzeta : qArrD W a b
      = Array.ofFn (n := dModel) fun r => qRow W a b r.val := rfl
  rw [hzeta, getD_ofFn' (g := qRow W a b) (fun _ => rfl) r hr]

private theorem scoreArrD_getD (e : ℕ) (he : e < nHeads * nPos) :
    (scoreArrD W a b).getD e .NaN = score W a b (e / nPos) (e % nPos) := by
  have hzeta : scoreArrD W a b
      = Array.ofFn (n := nHeads * nPos)
          (fun e => scoreEntry W a b (qArrD W a b) e.val) := rfl
  rw [hzeta,
    getD_ofFn' (g := scoreEntry W a b (qArrD W a b)) (fun _ => rfl) e he]
  have hs : seqDot dHead
      (fun h => kRow W a b (e / nPos * dHead + h) (e % nPos))
      (fun h => (qArrD W a b).getD (e / nPos * dHead + h) .NaN)
      = seqDot dHead
        (fun h => kRow W a b (e / nPos * dHead + h) (e % nPos))
        (fun h => qRow W a b (e / nPos * dHead + h)) :=
    seqDot_congr (fun h _ => rfl)
      (fun h hh => qArrD_getD W a b _ (by
        simp only [nPos_eq, dHead_eq, nHeads_eq, dModel_eq] at he hh ⊢
        omega))
  unfold scoreEntry score
  rw [hs]

private theorem scoreArrD_getD' (i pos : ℕ) (hi : i < nHeads)
    (hpos : pos < nPos) :
    (scoreArrD W a b).getD (i * nPos + pos) .NaN = score W a b i pos := by
  have hdiv : (i * nPos + pos) / nPos = i := by
    simp only [nPos_eq] at hpos ⊢; omega
  have hmod : (i * nPos + pos) % nPos = pos := by
    simp only [nPos_eq] at hpos ⊢; omega
  rw [scoreArrD_getD W a b _ (by
      simp only [nPos_eq, nHeads_eq] at hi hpos ⊢; omega),
    hdiv, hmod]

private theorem scoreArrD_getD0 (i : ℕ) (hi : i < nHeads) :
    (scoreArrD W a b).getD (i * nPos) .NaN = score W a b i 0 := by
  have h := scoreArrD_getD' W a b i 0 hi (by simp only [nPos_eq]; omega)
  simpa using h

private theorem expArrD_getD (e : ℕ) (he : e < nHeads * nPos) :
    (expArrD W a b).getD e .NaN = expScore W a b (e / nPos) (e % nPos) := by
  have hzeta : expArrD W a b
      = Array.ofFn (n := nHeads * nPos)
          (fun e => expEntry (scoreArrD W a b) e.val) := rfl
  rw [hzeta, getD_ofFn' (g := expEntry (scoreArrD W a b)) (fun _ => rfl) e he]
  have hi : e / nPos < nHeads := by
    simp only [nPos_eq, nHeads_eq] at he ⊢; omega
  unfold expEntry expScore smax
  rw [scoreArrD_getD W a b e he,
    scoreArrD_getD0 W a b (e / nPos) hi,
    scoreArrD_getD' W a b (e / nPos) 1 hi (by simp only [nPos_eq]; omega),
    scoreArrD_getD' W a b (e / nPos) 2 hi (by simp only [nPos_eq]; omega)]

private theorem expArrD_getD' (i pos : ℕ) (hi : i < nHeads)
    (hpos : pos < nPos) :
    (expArrD W a b).getD (i * nPos + pos) .NaN = expScore W a b i pos := by
  have hdiv : (i * nPos + pos) / nPos = i := by
    simp only [nPos_eq] at hpos ⊢; omega
  have hmod : (i * nPos + pos) % nPos = pos := by
    simp only [nPos_eq] at hpos ⊢; omega
  rw [expArrD_getD W a b _ (by
      simp only [nPos_eq, nHeads_eq] at hi hpos ⊢; omega),
    hdiv, hmod]

private theorem expArrD_getD0 (i : ℕ) (hi : i < nHeads) :
    (expArrD W a b).getD (i * nPos) .NaN = expScore W a b i 0 := by
  have h := expArrD_getD' W a b i 0 hi (by simp only [nPos_eq]; omega)
  simpa using h

private theorem attnArrD_getD (e : ℕ) (he : e < nHeads * nPos) :
    (attnArrD W a b).getD e .NaN = attnW W a b (e / nPos) (e % nPos) := by
  have hzeta : attnArrD W a b
      = Array.ofFn (n := nHeads * nPos)
          (fun e => attnEntry (expArrD W a b) e.val) := rfl
  rw [hzeta, getD_ofFn' (g := attnEntry (expArrD W a b)) (fun _ => rfl) e he]
  have hi : e / nPos < nHeads := by
    simp only [nPos_eq, nHeads_eq] at he ⊢; omega
  unfold attnEntry attnW denom
  rw [expArrD_getD W a b e he,
    expArrD_getD0 W a b (e / nPos) hi,
    expArrD_getD' W a b (e / nPos) 1 hi (by simp only [nPos_eq]; omega),
    expArrD_getD' W a b (e / nPos) 2 hi (by simp only [nPos_eq]; omega)]

private theorem zArrD_getD (r : ℕ) (hr : r < dModel) :
    (zArrD W a b).getD r .NaN = zRow W a b r := by
  have hzeta : zArrD W a b
      = Array.ofFn (n := dModel)
          (fun r => zEntry W a b (attnArrD W a b) r.val) := rfl
  rw [hzeta, getD_ofFn' (g := zEntry W a b (attnArrD W a b)) (fun _ => rfl) r hr]
  have hi : r / dHead < nHeads := by
    simp only [dHead_eq, nHeads_eq, dModel_eq] at hr ⊢; omega
  unfold zEntry zRow
  exact seqDot_congr (fun pos _ => rfl)
    (fun pos hpos => by
      have hdiv : (r / dHead * nPos + pos) / nPos = r / dHead := by
        simp only [nPos_eq] at hpos ⊢; omega
      have hmod : (r / dHead * nPos + pos) % nPos = pos := by
        simp only [nPos_eq] at hpos ⊢; omega
      rw [attnArrD_getD W a b _ (by
          simp only [nPos_eq, nHeads_eq] at hi hpos ⊢; omega),
        hdiv, hmod])

private theorem midArrD_getD (d : ℕ) (hd : d < dModel) :
    (midArrD W a b).getD d .NaN = residMidF W a b d := by
  have hzeta : midArrD W a b
      = Array.ofFn (n := dModel)
          (fun d => midEntry W a b (zArrD W a b) d.val) := rfl
  rw [hzeta, getD_ofFn' (g := midEntry W a b (zArrD W a b)) (fun _ => rfl) d hd]
  unfold midEntry residMidF attnOutF
  have hs : seqDot dModel (fun f => (zArrD W a b).getD f .NaN)
      (fun f => decode (W.wO.getD (d * dModel + f) 0))
      = seqDot dModel (zRow W a b)
        (fun f => decode (W.wO.getD (d * dModel + f) 0)) :=
    seqDot_congr (fun f hf => zArrD_getD W a b f hf) (fun f _ => rfl)
  rw [hs]

private theorem hidEntry_eq (m : ℕ) :
    hidEntry W (midArrD W a b) m = hiddenF W a b m := by
  unfold hidEntry hiddenF
  have hs : seqDot dModel (fun k => (midArrD W a b).getD k .NaN)
      (fun k => decode (W.wIn.getD (m * dModel + k) 0))
      = seqDot dModel (residMidF W a b)
        (fun k => decode (W.wIn.getD (m * dModel + k) 0)) :=
    seqDot_congr (fun k hk => midArrD_getD W a b k hk) (fun k _ => rfl)
  rw [hs]

private theorem outEntryF_eq (d : ℕ) (hd : d < dModel) :
    outEntryF W (midArrD W a b)
      (Array.ofFn (n := dMlp) fun m => hidEntry W (midArrD W a b) m.val) d
      = outF W a b d := by
  unfold outEntryF outF
  have hhid : ∀ m, m < dMlp →
      (Array.ofFn (n := dMlp)
        fun m => hidEntry W (midArrD W a b) m.val).getD m .NaN
      = hiddenF W a b m := fun m hm => by
    rw [getD_ofFn' (g := hidEntry W (midArrD W a b)) (fun _ => rfl) m hm]
    exact hidEntry_eq W a b m
  have hs : seqDot dMlp (fun m => decode (W.wOut.getD (d * dMlp + m) 0))
      (fun m => (Array.ofFn (n := dMlp)
        fun m => hidEntry W (midArrD W a b) m.val).getD m .NaN)
      = seqDot dMlp (fun m => decode (W.wOut.getD (d * dMlp + m) 0))
        (hiddenF W a b) :=
    seqDot_congr (fun m _ => rfl) hhid
  rw [hs, midArrD_getD W a b d hd]

private theorem rowLogitsFull_getD (j : ℕ) (hj : j < vocab) :
    (rowLogitsFull W a b).getD j .NaN = fullLogit W a b j := by
  have hzeta : rowLogitsFull W a b
      = Array.ofFn (n := vocab) fun j =>
          logitEntryF W
            (Array.ofFn (n := dModel) fun d =>
              outEntryF W (midArrD W a b)
                (Array.ofFn (n := dMlp)
                  fun m => hidEntry W (midArrD W a b) m.val) d.val)
            j.val := rfl
  rw [hzeta,
    getD_ofFn'
      (g := logitEntryF W
        (Array.ofFn (n := dModel) fun d =>
          outEntryF W (midArrD W a b)
            (Array.ofFn (n := dMlp)
              fun m => hidEntry W (midArrD W a b) m.val) d.val))
      (fun _ => rfl) j hj]
  unfold logitEntryF fullLogit
  exact seqDot_congr
    (fun k hk => by
      rw [getD_ofFn'
        (g := outEntryF W (midArrD W a b)
          (Array.ofFn (n := dMlp)
            fun m => hidEntry W (midArrD W a b) m.val))
        (fun _ => rfl) k hk]
      exact outEntryF_eq W a b k hk)
    (fun k _ => rfl)

/-- **Soundness**: if the compiled checker accepts a weight bundle, the
spec-Binary32 forward pass of that network computes modular addition —
parametric over all weights. -/
theorem checkFullNet_sound (h : checkFullNet W = true) : FullNetCorrect W := by
  intro a ha b hb j hj hne
  unfold checkFullNet at h
  rw [List.all_eq_true] at h
  have htask : (Task.spawn fun _ => checkRowsForAFull W a).get = true :=
    h _ (List.mem_map_of_mem (List.mem_range.mpr ha))
  rw [get_spawn_const] at htask
  unfold checkRowsForAFull at htask
  rw [List.all_eq_true] at htask
  exact checkRow_sound' (rowLogitsFull W a b) (fullLogit W a b)
    (fun j hj => rowLogitsFull_getD W a b j hj)
    ((a + b) % p)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [p])) (by norm_num [p, vocab]))
    (htask b (List.mem_range.mpr hb)) j hj hne

end Soundness

end Flean.Checker.ModAdd
