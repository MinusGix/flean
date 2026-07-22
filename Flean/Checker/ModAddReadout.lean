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

/-! ## Fast native Binary32 decoder (compiler-only optimization)

`Fp.ofBits` is written for proof convenience: it slices the word with
`BitVec.extractLsb'` (arbitrary-precision `Nat` shifts and `% 2^n`, i.e. GMP
traffic on every call) and decides the *propositions* `isNaN` / `isInfinite`
by `BitVec.allOnes` comparisons.  `decodeFast` below performs the identical
decoding with three native `UInt32` shift/mask operations, and
`decode_eq_decodeFast` (a `@[csimp]` lemma) makes the compiler use it.
The *definition* of `decode` — and hence every theorem about it — is untouched;
only generated code changes.  Constants below are the Binary32 field widths,
each discharged by `decide` against the `instB32` instance rather than assumed.
-/

section DecodeFast

open Fp

private theorem b32_bitSize : FloatFormat.bitSize = 32 := by decide
private theorem b32_expBits : FloatFormat.exponentBits = 8 := by decide
private theorem b32_sigBits : FloatFormat.significandBits = 23 := by decide
private theorem b32_signBits : FloatFormat.signBits = 1 := rfl
private theorem b32_bias : (FloatFormat.exponentBias : ℤ) = 127 := by decide
private theorem b32_min_exp : (FloatFormat.min_exp : ℤ) = -126 := by decide
private theorem b32_max_exp : (FloatFormat.max_exp : ℤ) = 127 := by decide
private theorem b32_prec_toNat : (FloatFormat.prec : ℤ).toNat = 24 := by decide
private theorem b32_prec_sub_one_toNat : ((FloatFormat.prec : ℤ) - 1).toNat = 23 := by decide

private theorem valid_sub (m : ℕ) (hm : m < 8388608) :
    IsValidFiniteVal (FloatFormat.min_exp) m := by
  refine ⟨le_refl _, FloatFormat.exp_order_le, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · rw [b32_prec_toNat]; omega
  · rw [b32_prec_sub_one_toNat]; omega

private theorem valid_norm (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 254) (m : ℕ) (hm : m < 8388608) :
    IsValidFiniteVal ((e : ℤ) - 127) (m + 8388608) := by
  refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [b32_min_exp]; omega
  · rw [b32_max_exp]; omega
  · rw [b32_prec_toNat]; omega
  · rw [b32_prec_sub_one_toNat]; omega
  · rw [b32_prec_toNat]; omega

/-! ### native field extraction -/

@[inline] def wSignBit (w : UInt32) : Bool := ((w >>> 31) &&& 1) == 1
@[inline] def wExp (w : UInt32) : UInt32 := (w >>> 23) &&& 0xff
@[inline] def wSig (w : UInt32) : UInt32 := w &&& 0x7fffff

private theorem wExp_toNat (w : UInt32) : (wExp w).toNat = w.toNat >>> 23 % 2 ^ 8 := by
  unfold wExp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight,
    show (UInt32.toNat 23 % 32) = 23 from rfl, show UInt32.toNat 255 = 2^8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem wSig_toNat (w : UInt32) : (wSig w).toNat = w.toNat % 2 ^ 23 := by
  unfold wSig
  rw [UInt32.toNat_and, show UInt32.toNat 8388607 = 2^23 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem wSignBit_toNat (w : UInt32) : ((w >>> 31) &&& 1).toNat = w.toNat >>> 31 % 2 := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, show (UInt32.toNat 31 % 32) = 31 from rfl,
    show UInt32.toNat 1 = 2^1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem uint32_beq_toNat (a b : UInt32) : (a == b) = (a.toNat == b.toNat) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : a.toNat ≠ b.toNat := fun hc => h (UInt32.toNat_inj.mp hc)
    simp [h, h2]

private theorem wSignBit_eq (w : UInt32) : wSignBit w = (w.toNat >>> 31 % 2 == 1) := by
  unfold wSignBit
  rw [uint32_beq_toNat, wSignBit_toNat]
  rfl

/-! ### triple extraction -/

private theorem triple_exp (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.exponent.toNat = (wExp w).toNat := by
  simp only [FloatBits.toBitsTriple, BitVec.extractLsb'_toNat, b32_bitSize, b32_expBits,
    b32_signBits, wExp_toNat]
  rfl

private theorem triple_sig (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.significand.toNat = (wSig w).toNat := by
  simp only [FloatBits.toBitsTriple, BitVec.extractLsb'_toNat, b32_sigBits, wSig_toNat]
  rfl

private theorem triple_sign (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.sign.toNat = w.toNat >>> 31 % 2 := by
  simp only [FloatBits.toBitsTriple, BitVec.extractLsb'_toNat, b32_bitSize, b32_signBits]
  rfl

private theorem wExp_le (w : UInt32) : (wExp w).toNat ≤ 255 := by
  rw [wExp_toNat]; omega

private theorem wSig_lt (w : UInt32) : (wSig w).toNat < 8388608 := by
  rw [wSig_toNat]; omega

/-- Fast Binary32 decoder built from native `UInt32` shifts and masks. -/
def decodeFast (w : UInt32) : Fp :=
  if h : wExp w = 255 then
    if wSig w = 0 then .infinite (wSignBit w) else .NaN
  else
    if h0' : wExp w = 0 then
      .finite ⟨wSignBit w, FloatFormat.min_exp, (wSig w).toNat, valid_sub _ (wSig_lt w)⟩
    else
      .finite ⟨wSignBit w, ((wExp w).toNat : ℤ) - 127, (wSig w).toNat + 8388608,
        valid_norm _ (by
          rcases Nat.eq_zero_or_pos (wExp w).toNat with h0 | h0
          · exact absurd (UInt32.toNat_inj.mp (by rw [h0]; rfl)) h0'
          · exact h0)
          (by have := wExp_le w
              have : (wExp w).toNat ≠ 255 := fun hc => h (UInt32.toNat_inj.mp (by rw [hc]; rfl))
              omega)
          _ (wSig_lt w)⟩

private theorem exp_eq_iff (w : UInt32) (n : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.exponent.toNat = n.toNat ↔ wExp w = n := by
  rw [triple_exp, UInt32.toNat_inj]

private theorem isExpAllOnes_iff (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).isExponentAllOnes ↔ wExp w = 255 := by
  rw [FloatBits.isExponentAllOnes_eq_ofNat,
    show (2 ^ FloatFormat.exponentBits - 1 : ℕ) = (255 : UInt32).toNat from by rw [b32_expBits]; rfl]
  exact exp_eq_iff w 255

private theorem isTSigZero_iff (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).isTSignificandZero ↔ wSig w = 0 := by
  unfold FloatBits.isTSignificandZero
  constructor
  · intro h; apply UInt32.toNat_inj.mp; rw [← triple_sig, h]; rfl
  · intro h; apply BitVec.toNat_inj.mp; rw [triple_sig, h]; rfl

private theorem exp_zero_iff (w : UInt32) :
    (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.exponent = 0 ↔ wExp w = 0 := by
  constructor
  · intro h; apply UInt32.toNat_inj.mp; rw [← triple_exp, h]; rfl
  · intro h; apply BitVec.toNat_inj.mp; rw [triple_exp, h]; rfl

private theorem sign_eq (w : UInt32) : (⟨w.toBitVec⟩ : FloatBits).sign = wSignBit w := by
  unfold FloatBits.sign
  rw [wSignBit_eq, ← triple_sign]
  by_cases hc : (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.sign.toNat = 1
  · have h1 : (⟨w.toBitVec⟩ : FloatBits).toBitsTriple.sign = 1 :=
      BitVec.toNat_inj.mp (by rw [hc]; rfl)
    simp [h1]
  · rw [show ((⟨w.toBitVec⟩ : FloatBits).toBitsTriple.sign == 1) = false from by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      exact hc (by rw [h]; rfl)]
    simp [hc]

private theorem sign_bit_eq (w : UInt32) :
    ((⟨w.toBitVec⟩ : FloatBits).toBitsTriple.sign.toNat == 1) = wSignBit w := by
  rw [wSignBit_eq, triple_sign]

private theorem FpExponent_of_zero (w : UInt32) (h : wExp w = 0) :
    (⟨w.toBitVec⟩ : FloatBits).FpExponent = FloatFormat.min_exp := by
  rw [FloatBits.FpExponent_def, if_pos ((exp_zero_iff w).mpr h)]

private theorem FpExponent_of_ne_zero (w : UInt32) (h : wExp w ≠ 0) :
    (⟨w.toBitVec⟩ : FloatBits).FpExponent = ((wExp w).toNat : ℤ) - 127 := by
  rw [FloatBits.FpExponent_def, if_neg (fun hc => h ((exp_zero_iff w).mp hc)), triple_exp,
    b32_bias]

private theorem FpSignificand_of_zero (w : UInt32) (h : wExp w = 0) :
    (⟨w.toBitVec⟩ : FloatBits).FpSignificand = (wSig w).toNat := by
  rw [FloatBits.FpSignificand_def, if_pos ((exp_zero_iff w).mpr h), triple_sig]

private theorem FpSignificand_of_ne_zero (w : UInt32) (h : wExp w ≠ 0) :
    (⟨w.toBitVec⟩ : FloatBits).FpSignificand = (wSig w).toNat + 8388608 := by
  rw [FloatBits.FpSignificand_def, if_neg (fun hc => h ((exp_zero_iff w).mp hc)),
    BitVec.toNat_append, Nat.shiftLeft_eq, show (BitVec.ofBool true).toNat = 1 from rfl, one_mul,
    triple_sig]
  have hlt : (wSig w).toNat < 2 ^ FloatFormat.significandBits := by
    rw [b32_sigBits]; exact wSig_lt w
  rw [b32_sigBits] at *
  rw [show (wSig w).toNat + 8388608 = 2^23 * 1 + (wSig w).toNat from by ring,
    Nat.two_pow_add_eq_or_of_lt hlt, mul_one]

@[csimp] theorem decode_eq_decodeFast : decode = decodeFast := by
  funext w
  unfold decode decodeFast Fp.ofBits
  by_cases hE : wExp w = 255
  · rw [dif_pos hE]
    by_cases hS : wSig w = 0
    · rw [if_pos hS]
      have hn : ¬ (⟨w.toBitVec⟩ : FloatBits).isNaN :=
        fun h => h.2 ((isTSigZero_iff w).mpr hS)
      have hi : (⟨w.toBitVec⟩ : FloatBits).isInfinite :=
        ⟨(isExpAllOnes_iff w).mpr hE, (isTSigZero_iff w).mpr hS⟩
      rw [dif_neg hn, dif_pos hi, sign_eq]
    · rw [if_neg hS]
      have hn : (⟨w.toBitVec⟩ : FloatBits).isNaN :=
        ⟨(isExpAllOnes_iff w).mpr hE, fun h => hS ((isTSigZero_iff w).mp h)⟩
      rw [dif_pos hn]
  · rw [dif_neg hE]
    have hEA : ¬ (⟨w.toBitVec⟩ : FloatBits).isExponentAllOnes :=
      fun h => hE ((isExpAllOnes_iff w).mp h)
    have hn : ¬ (⟨w.toBitVec⟩ : FloatBits).isNaN := fun h => hEA h.1
    have hi : ¬ (⟨w.toBitVec⟩ : FloatBits).isInfinite := fun h => hEA h.1
    rw [dif_neg hn, dif_neg hi]
    by_cases h0 : wExp w = 0
    · rw [dif_pos h0]
      exact congrArg Fp.finite
        (FiniteFp.ext (sign_bit_eq w) (FpExponent_of_zero w h0) (FpSignificand_of_zero w h0))
    · rw [dif_neg h0]
      exact congrArg Fp.finite
        (FiniteFp.ext (sign_bit_eq w) (FpExponent_of_ne_zero w h0) (FpSignificand_of_ne_zero w h0))

end DecodeFast

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
