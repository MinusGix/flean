import Flean.Encoding.Conversion
import Flean.Operations.Add
import Flean.Operations.Mul
import Flean.Rounding.PolicyInstances
import Flean.Checker.RawTensor

/-!
# Verified readout checker for the grokked mod-113 network

First instance of the verified-checker pattern (`docs/verified_checker_design.md`):
the checkpoint is *data*, the checker is a *proven program*.

Given two raw word arrays — the final-position residual stream `resid` (one row
of 128 Binary32 words per input pair `(a, b)`, row index `a * 113 + b`) and the
unembedding matrix `W_U` (128 × 114) — the checker recomputes every logit as a
**specification-exact Binary32 dot product** (Flean's `fpMul`/`fpAdd` under
round-to-nearest-even, sequential left-to-right order) and verifies that the
logit of the true answer `(a + b) % 113` strictly exceeds every other logit,
in exact rational comparison of decoded values.

`checkReadout_sound` is parametric over ALL word arrays: `checkReadout resid wU
= true → ReadoutCorrect resid wU`. Running the compiled checker on the on-disk
tensors then establishes `ReadoutCorrect` for the actual checkpoint at the
trust level of the Lean compiler plus the file-reading boundary — deliberately
not a kernel theorem about the particular bytes.

What is trusted about the *data*: that `resid` really is the residual stream
the reference float32 forward pass produces (exported by
`references/export_activations.py`). The unembed layer itself is not trusted:
its arithmetic is re-executed inside the Lean spec. Extending the recomputation
upstream through the MLP and attention layers replaces that trust step by step.
-/

namespace Flean.Checker.ModAdd

local instance instB32 : StdFloatFormat := FloatFormat.Binary32
local instance : UseRoundingPolicy RoundNearestEvenPolicy := ⟨⟩

/-- The modulus. -/
def p : ℕ := 113
/-- Residual-stream width. -/
def dModel : ℕ := 128
/-- Number of output classes (`0 … 112` and `'='`). -/
def vocab : ℕ := 114

/-- Decode a raw little-endian word through Flean's IEEE Binary32 decoder. -/
def decode (w : UInt32) : Fp := Fp.ofBits ⟨w.toBitVec⟩

/-- Specification logit: the sequential Binary32 dot product of residual row
`i` with unembed column `j`, one rounded multiply and one rounded add per
coordinate, left-to-right. Any non-finite intermediate propagates. -/
def specLogit (resid wU : Array UInt32) (i j : ℕ) : Fp :=
  (List.range dModel).foldl
    (fun acc k =>
      fpAdd acc (fpMul (decode (resid.getD (i * dModel + k) 0))
                       (decode (wU.getD (k * vocab + j) 0))))
    (.finite 0)

/-- The network's readout decodes modular addition: for every input pair the
true-answer logit is finite and strictly exceeds every other logit (exact
rational comparison of the decoded Binary32 values). -/
def ReadoutCorrect (resid wU : Array UInt32) : Prop :=
  ∀ a, a < p → ∀ b, b < p → ∀ j, j < vocab → j ≠ (a + b) % p →
    ∃ ft fw : FiniteFp,
      specLogit resid wU (a * p + b) ((a + b) % p) = .finite ft ∧
      specLogit resid wU (a * p + b) j = .finite fw ∧
      fw.toRat < ft.toRat

/-- Decoded exact rational value of a finite `Fp` (reporting helper). -/
def fpToRat? : Fp → Option ℚ
  | .finite f => some f.toRat
  | _ => none

/-! ## Executable checker -/

/-- All `vocab` logits of row `i`, each computed once. -/
def rowLogits (resid wU : Array UInt32) (i : ℕ) : Array Fp :=
  Array.ofFn (n := vocab) fun j => specLogit resid wU i j.val

/-- Check one row: the label logit is finite and strictly beats every other
(finite) logit. -/
def checkRow (row : Array Fp) (lab : ℕ) : Bool :=
  match row.getD lab .NaN with
  | .finite ft =>
    (List.range vocab).all fun j =>
      j = lab ||
        match row.getD j .NaN with
        | .finite fw => decide (fw.toRat < ft.toRat)
        | _ => false
  | _ => false

/-- The checker: recompute and verify every row. -/
def checkReadout (resid wU : Array UInt32) : Bool :=
  (List.range p).all fun a =>
    (List.range p).all fun b =>
      checkRow (rowLogits resid wU (a * p + b)) ((a + b) % p)

/-! ## Soundness -/

private theorem rowLogits_getD (resid wU : Array UInt32) (i j : ℕ)
    (hj : j < vocab) :
    (rowLogits resid wU i).getD j .NaN = specLogit resid wU i j := by
  have hsz : j < (rowLogits resid wU i).size := by
    simpa [rowLogits] using hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
  simp [rowLogits]

private theorem checkRow_sound (resid wU : Array UInt32) (i lab : ℕ)
    (hlab : lab < vocab)
    (h : checkRow (rowLogits resid wU i) lab = true) :
    ∀ j, j < vocab → j ≠ lab →
      ∃ ft fw : FiniteFp,
        specLogit resid wU i lab = .finite ft ∧
        specLogit resid wU i j = .finite fw ∧
        fw.toRat < ft.toRat := by
  intro j hj hne
  unfold checkRow at h
  rw [rowLogits_getD resid wU i lab hlab] at h
  split at h
  case _ ft hft =>
    rw [List.all_eq_true] at h
    have hjmem : j ∈ List.range vocab := List.mem_range.mpr hj
    have hj' := h j hjmem
    rw [Bool.or_eq_true, decide_eq_true_eq] at hj'
    rcases hj' with hj' | hj'
    · exact absurd hj' hne
    · rw [rowLogits_getD resid wU i j hj] at hj'
      split at hj'
      case _ fw hfw =>
        exact ⟨ft, fw, hft, hfw, of_decide_eq_true hj'⟩
      case _ => exact absurd hj' (by simp)
  case _ => exact absurd h (by simp)

/-- **Soundness**: if the compiled checker accepts the word arrays, the
readout decodes modular addition — parametric over all inputs. -/
theorem checkReadout_sound (resid wU : Array UInt32)
    (h : checkReadout resid wU = true) : ReadoutCorrect resid wU := by
  intro a ha b hb j hj hne
  unfold checkReadout at h
  rw [List.all_eq_true] at h
  have hrow := h a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at hrow
  have hrow := hrow b (List.mem_range.mpr hb)
  exact checkRow_sound resid wU (a * p + b) ((a + b) % p)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [p])) (by norm_num [p, vocab]))
    hrow j hj hne

end Flean.Checker.ModAdd
