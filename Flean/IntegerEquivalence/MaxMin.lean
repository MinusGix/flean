import Flean.IntegerEquivalence.Compare
import Flean.Operations.Softmax

/-! # FP ↔ Integer equivalence: `fpMax` / `fpMin` ↔ bit-pattern argmax/argmin

Phase 2 closure of the FP ↔ Integer equivalence area.

`Compare.lean` shipped four `<`-bridges between `Fp` ordering and unsigned
bit comparison (under sign carve-outs, sub-tolerant). This file lifts those
to the vector level: for nonneg (resp. nonpos) finite inputs, `fpMax xs hn`
(resp. `fpMin xs hn`) coincides with the value at the index that maximizes
(resp. minimizes) the unsigned bit pattern. Equivalently, FP-argmax can be
implemented in the integer pipeline via integer-argmax on the bit patterns.

The headlines take an `i : Fin n` already attaining the bit-argmax (or
argmin) and conclude `fpMax xs hn = xs i` — callers compute the index via
their preferred integer-pipeline argmax routine and apply.

Why nonneg/nonpos carve-out, not full signed: for mixed-sign inputs the
sign bit dominates and the unsigned bit comparison flips at the boundary
(positives are ascending, negatives are descending in magnitude, with
`-0 < +0` as a corner). The sign-magnitude `totalOrder` formula in
`TotalOrder.lean` handles the full mixed-sign case; this file is the
clean unsigned-pipeline result for already-sorted-sign inputs. -/

namespace Fp

variable [StdFloatFormat]

/-! ## Companion `≤`-bridges (corollaries of `<`-bridges) -/

/-- For two non-negative finite `FloatBits`, IEEE 754 `Fp ≤` agrees with
unsigned integer `≤` on the bit pattern. Derived from the existing `<`
bridge via the FiniteFp linear order: `f₁ ≤ f₂ ↔ ¬(f₂ < f₁)`. -/
theorem ofBits_le_iff_b_toNat_le_of_finite_nonneg
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hs₁ : b₁.sign = false) (hs₂ : b₂.sign = false) :
    ofBits b₁ ≤ ofBits b₂ ↔ b₁.b.toNat ≤ b₂.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₁⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₂⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_isFinite b₁ hf₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_isFinite b₂ hf₂
  rw [hofb₁, hofb₂, finite_le_finite_iff]
  -- f₁ ≤ f₂ ↔ ¬(f₂ < f₁), then ↔ ¬(Fp.finite f₂ < Fp.finite f₁)
  -- ↔ ¬(b₂.b.toNat < b₁.b.toNat) ↔ b₁.b.toNat ≤ b₂.b.toNat.
  rw [show (f₁ ≤ f₂) ↔ ¬(f₂ < f₁) from (not_lt (a := f₂) (b := f₁)).symm]
  rw [show (f₂ < f₁) ↔ Fp.finite f₂ < Fp.finite f₁ from by
    show f₂ < f₁ ↔ Fp.is_total_lt (Fp.finite f₂) (Fp.finite f₁)
    show f₂ < f₁ ↔ f₂ < f₁
    exact Iff.rfl]
  rw [← hofb₁, ← hofb₂]
  rw [ofBits_lt_iff_b_toNat_lt_of_finite_nonneg b₂ b₁ hf₂ hf₁ hs₂ hs₁]
  omega

/-- For two non-positive finite `FloatBits`, IEEE 754 `Fp ≤` is anti-monotone
in unsigned bit comparison (larger bits = larger magnitude = smaller value). -/
theorem ofBits_le_iff_b_toNat_ge_of_finite_nonpos
    (b₁ b₂ : FloatBits) (hf₁ : b₁.isFinite) (hf₂ : b₂.isFinite)
    (hs₁ : b₁.sign = true) (hs₂ : b₂.sign = true) :
    ofBits b₁ ≤ ofBits b₂ ↔ b₂.b.toNat ≤ b₁.b.toNat := by
  set f₁ : FiniteFp := ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₁⟩
  set f₂ : FiniteFp := ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
    FloatBits.isFinite_validFloatVal hf₂⟩
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := ofBits_eq_finite_of_isFinite b₁ hf₁
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := ofBits_eq_finite_of_isFinite b₂ hf₂
  rw [hofb₁, hofb₂, finite_le_finite_iff]
  rw [show (f₁ ≤ f₂) ↔ ¬(f₂ < f₁) from (not_lt (a := f₂) (b := f₁)).symm]
  rw [show (f₂ < f₁) ↔ Fp.finite f₂ < Fp.finite f₁ from by
    show f₂ < f₁ ↔ Fp.is_total_lt (Fp.finite f₂) (Fp.finite f₁)
    show f₂ < f₁ ↔ f₂ < f₁
    exact Iff.rfl]
  rw [← hofb₁, ← hofb₂]
  rw [ofBits_lt_iff_b_toNat_gt_of_finite_nonpos b₂ b₁ hf₂ hf₁ hs₂ hs₁]
  omega

end Fp

/-! ## `fpMax` / `fpMin` headlines

Lift the bit-level `≤` correspondence to the vector level. For nonneg
(resp. nonpos) inputs, `fpMax`/`fpMin` (defined via `Finset.sup'`/`inf'`
on the FP order) coincides with the value at the bit-argmax (resp.
bit-argmin) index. -/

open Softmax

namespace Fp

/-- Bridge `FiniteFp ≤` ↔ unsigned bit comparison for nonneg pair of
`FiniteFp` values, going through `FloatBits.finite` encoding. -/
theorem FiniteFp_le_iff_finite_b_toNat_le_of_nonneg
    [StdFloatFormat]
    (f₁ f₂ : FiniteFp) (hs₁ : f₁.s = false) (hs₂ : f₂.s = false) :
    f₁ ≤ f₂ ↔
      (FloatBits.finite f₁.s f₁.e f₁.m f₁.valid).b.toNat ≤
      (FloatBits.finite f₂.s f₂.e f₂.m f₂.valid).b.toNat := by
  set b₁ := FloatBits.finite f₁.s f₁.e f₁.m f₁.valid
  set b₂ := FloatBits.finite f₂.s f₂.e f₂.m f₂.valid
  have hf₁ : b₁.isFinite :=
    FloatBits.finite_isFinite f₁.s f₁.e f₁.m StdFloatFormat.st f₁.valid
  have hf₂ : b₂.isFinite :=
    FloatBits.finite_isFinite f₂.s f₂.e f₂.m StdFloatFormat.st f₂.valid
  have hs₁_b : b₁.sign = false := by
    show (FloatBits.finite f₁.s f₁.e f₁.m f₁.valid).sign = false
    rw [FloatBits.finite_sign]; exact hs₁
  have hs₂_b : b₂.sign = false := by
    show (FloatBits.finite f₂.s f₂.e f₂.m f₂.valid).sign = false
    rw [FloatBits.finite_sign]; exact hs₂
  -- ofBits b₁ = Fp.finite f₁ (via decoded sign/exp/sig matches f's data).
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := by
    have hofb : ofBits b₁ = Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₁⟩ :=
      ofBits_eq_finite_of_isFinite b₁ hf₁
    rw [hofb]; congr 1
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · show b₁.sign = f₁.s; rw [hs₁_b, hs₁]
    · exact FloatBits.finite_FpExponent f₁.valid
    · exact FloatBits.finite_FpSignificand f₁.valid
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := by
    have hofb : ofBits b₂ = Fp.finite ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₂⟩ :=
      ofBits_eq_finite_of_isFinite b₂ hf₂
    rw [hofb]; congr 1
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · show b₂.sign = f₂.s; rw [hs₂_b, hs₂]
    · exact FloatBits.finite_FpExponent f₂.valid
    · exact FloatBits.finite_FpSignificand f₂.valid
  -- ofBits b₁ ≤ ofBits b₂ ↔ Fp.finite f₁ ≤ Fp.finite f₂ ↔ f₁ ≤ f₂.
  rw [show f₁ ≤ f₂ ↔ ofBits b₁ ≤ ofBits b₂ from by
    rw [hofb₁, hofb₂]; exact (Fp.finite_le_finite_iff f₁ f₂).symm]
  exact ofBits_le_iff_b_toNat_le_of_finite_nonneg b₁ b₂ hf₁ hf₂ hs₁_b hs₂_b

/-- Anti-monotone `FiniteFp ≤` for nonpos pair: smaller bit pattern means
larger FP value (less negative magnitude). -/
theorem FiniteFp_le_iff_finite_b_toNat_ge_of_nonpos
    [StdFloatFormat]
    (f₁ f₂ : FiniteFp) (hs₁ : f₁.s = true) (hs₂ : f₂.s = true) :
    f₁ ≤ f₂ ↔
      (FloatBits.finite f₂.s f₂.e f₂.m f₂.valid).b.toNat ≤
      (FloatBits.finite f₁.s f₁.e f₁.m f₁.valid).b.toNat := by
  set b₁ := FloatBits.finite f₁.s f₁.e f₁.m f₁.valid
  set b₂ := FloatBits.finite f₂.s f₂.e f₂.m f₂.valid
  have hf₁ : b₁.isFinite :=
    FloatBits.finite_isFinite f₁.s f₁.e f₁.m StdFloatFormat.st f₁.valid
  have hf₂ : b₂.isFinite :=
    FloatBits.finite_isFinite f₂.s f₂.e f₂.m StdFloatFormat.st f₂.valid
  have hs₁_b : b₁.sign = true := by
    show (FloatBits.finite f₁.s f₁.e f₁.m f₁.valid).sign = true
    rw [FloatBits.finite_sign]; exact hs₁
  have hs₂_b : b₂.sign = true := by
    show (FloatBits.finite f₂.s f₂.e f₂.m f₂.valid).sign = true
    rw [FloatBits.finite_sign]; exact hs₂
  have hofb₁ : ofBits b₁ = Fp.finite f₁ := by
    have hofb : ofBits b₁ = Fp.finite ⟨b₁.sign, b₁.FpExponent, b₁.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₁⟩ :=
      ofBits_eq_finite_of_isFinite b₁ hf₁
    rw [hofb]; congr 1
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · show b₁.sign = f₁.s; rw [hs₁_b, hs₁]
    · exact FloatBits.finite_FpExponent f₁.valid
    · exact FloatBits.finite_FpSignificand f₁.valid
  have hofb₂ : ofBits b₂ = Fp.finite f₂ := by
    have hofb : ofBits b₂ = Fp.finite ⟨b₂.sign, b₂.FpExponent, b₂.FpSignificand,
      FloatBits.isFinite_validFloatVal hf₂⟩ :=
      ofBits_eq_finite_of_isFinite b₂ hf₂
    rw [hofb]; congr 1
    apply (FiniteFp.eq_def _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · show b₂.sign = f₂.s; rw [hs₂_b, hs₂]
    · exact FloatBits.finite_FpExponent f₂.valid
    · exact FloatBits.finite_FpSignificand f₂.valid
  rw [show f₁ ≤ f₂ ↔ ofBits b₁ ≤ ofBits b₂ from by
    rw [hofb₁, hofb₂]; exact (Fp.finite_le_finite_iff f₁ f₂).symm]
  exact ofBits_le_iff_b_toNat_ge_of_finite_nonpos b₁ b₂ hf₁ hf₂ hs₁_b hs₂_b

/-! ### `fpMax` / `fpMin` ↔ bit-argmax / bit-argmin -/

/-- **Bit-argmax = FP-argmax (nonneg).** For a nonneg vector of `FiniteFp`
values, any index `i` that attains the maximum unsigned bit pattern also
attains the FP-max. -/
theorem fpMax_eq_of_bit_argmax_nonneg
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_nn : ∀ i, (xs i).s = false)
    (i : Fin n)
    (h_max : ∀ j,
      (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat ≤
      (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat) :
    fpMax xs hn = xs i := by
  -- xs j ≤ xs i for all j (via the bit-bridge).
  have h_le : ∀ j, xs j ≤ xs i := by
    intro j
    rw [FiniteFp_le_iff_finite_b_toNat_le_of_nonneg (xs j) (xs i) (h_nn j) (h_nn i)]
    exact h_max j
  -- Now Finset.sup' xs ≤ xs i and xs i ≤ Finset.sup' xs.
  unfold fpMax
  exact _root_.le_antisymm
    (Finset.sup'_le _ xs (fun j _ => h_le j))
    (Finset.le_sup' xs (Finset.mem_univ i))

/-- **Bit-argmin = FP-argmin (nonneg).** For a nonneg vector, any index
attaining the minimum unsigned bit pattern also attains the FP-min. -/
theorem fpMin_eq_of_bit_argmin_nonneg
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_nn : ∀ i, (xs i).s = false)
    (i : Fin n)
    (h_min : ∀ j,
      (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat ≤
      (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat) :
    fpMin xs hn = xs i := by
  have h_le : ∀ j, xs i ≤ xs j := by
    intro j
    rw [FiniteFp_le_iff_finite_b_toNat_le_of_nonneg (xs i) (xs j) (h_nn i) (h_nn j)]
    exact h_min j
  unfold fpMin
  exact _root_.le_antisymm
    (Finset.inf'_le xs (Finset.mem_univ i))
    (Finset.le_inf' _ xs (fun j _ => h_le j))

/-- **Anti-mono bit-argmin = FP-argmax (nonpos).** For a nonpos vector,
the FP-max is attained at the index with the *minimum* unsigned bit
pattern (smallest magnitude = closest to zero = least negative). -/
theorem fpMax_eq_of_bit_argmin_nonpos
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_np : ∀ i, (xs i).s = true)
    (i : Fin n)
    (h_min : ∀ j,
      (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat ≤
      (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat) :
    fpMax xs hn = xs i := by
  have h_le : ∀ j, xs j ≤ xs i := by
    intro j
    rw [FiniteFp_le_iff_finite_b_toNat_ge_of_nonpos (xs j) (xs i) (h_np j) (h_np i)]
    exact h_min j
  unfold fpMax
  exact _root_.le_antisymm
    (Finset.sup'_le _ xs (fun j _ => h_le j))
    (Finset.le_sup' xs (Finset.mem_univ i))

/-- **Anti-mono bit-argmax = FP-argmin (nonpos).** For a nonpos vector,
the FP-min is attained at the index with the *maximum* unsigned bit
pattern (largest magnitude = furthest from zero = most negative). -/
theorem fpMin_eq_of_bit_argmax_nonpos
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_np : ∀ i, (xs i).s = true)
    (i : Fin n)
    (h_max : ∀ j,
      (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat ≤
      (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat) :
    fpMin xs hn = xs i := by
  have h_le : ∀ j, xs i ≤ xs j := by
    intro j
    rw [FiniteFp_le_iff_finite_b_toNat_ge_of_nonpos (xs i) (xs j) (h_np i) (h_np j)]
    exact h_max j
  unfold fpMin
  exact _root_.le_antisymm
    (Finset.inf'_le xs (Finset.mem_univ i))
    (Finset.le_inf' _ xs (fun j _ => h_le j))

/-! ### Existence wrappers (auto-derive the index)

For callers that don't have a pre-computed argmax/argmin index, these
existence variants apply `Finset.exists_max_image`/`exists_min_image` on the
bit-pattern function and feed the resulting index back through the
positional headlines above. -/

/-- **Existence (nonneg).** `fpMax xs hn` is attained at some index that's
also a bit-argmax. -/
theorem fpMax_eq_bit_argmax_nonneg
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_nn : ∀ i, (xs i).s = false) :
    ∃ i₀ : Fin n, fpMax xs hn = xs i₀ ∧
      ∀ j,
        (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat ≤
        (FloatBits.finite (xs i₀).s (xs i₀).e (xs i₀).m (xs i₀).valid).b.toNat := by
  let g : Fin n → ℕ := fun i =>
    (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨i₀, _, h_max⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n)) g h_ne
  refine ⟨i₀, ?_, fun j => h_max j (Finset.mem_univ j)⟩
  exact fpMax_eq_of_bit_argmax_nonneg xs hn h_nn i₀
    (fun j => h_max j (Finset.mem_univ j))

/-- **Existence (nonneg).** `fpMin xs hn` is attained at some index that's
also a bit-argmin. -/
theorem fpMin_eq_bit_argmin_nonneg
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_nn : ∀ i, (xs i).s = false) :
    ∃ i₀ : Fin n, fpMin xs hn = xs i₀ ∧
      ∀ j,
        (FloatBits.finite (xs i₀).s (xs i₀).e (xs i₀).m (xs i₀).valid).b.toNat ≤
        (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat := by
  let g : Fin n → ℕ := fun i =>
    (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨i₀, _, h_min⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin n)) g h_ne
  refine ⟨i₀, ?_, fun j => h_min j (Finset.mem_univ j)⟩
  exact fpMin_eq_of_bit_argmin_nonneg xs hn h_nn i₀
    (fun j => h_min j (Finset.mem_univ j))

/-- **Existence (nonpos).** `fpMax xs hn` is attained at the bit-argmin
index (smallest bit pattern = closest to zero = least negative). -/
theorem fpMax_eq_bit_argmin_nonpos
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_np : ∀ i, (xs i).s = true) :
    ∃ i₀ : Fin n, fpMax xs hn = xs i₀ ∧
      ∀ j,
        (FloatBits.finite (xs i₀).s (xs i₀).e (xs i₀).m (xs i₀).valid).b.toNat ≤
        (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat := by
  let g : Fin n → ℕ := fun i =>
    (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨i₀, _, h_min⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin n)) g h_ne
  refine ⟨i₀, ?_, fun j => h_min j (Finset.mem_univ j)⟩
  exact fpMax_eq_of_bit_argmin_nonpos xs hn h_np i₀
    (fun j => h_min j (Finset.mem_univ j))

/-- **Existence (nonpos).** `fpMin xs hn` is attained at the bit-argmax
index (largest bit pattern = furthest from zero = most negative). -/
theorem fpMin_eq_bit_argmax_nonpos
    [StdFloatFormat]
    {n : ℕ} (xs : Fin n → FiniteFp) (hn : 0 < n)
    (h_np : ∀ i, (xs i).s = true) :
    ∃ i₀ : Fin n, fpMin xs hn = xs i₀ ∧
      ∀ j,
        (FloatBits.finite (xs j).s (xs j).e (xs j).m (xs j).valid).b.toNat ≤
        (FloatBits.finite (xs i₀).s (xs i₀).e (xs i₀).m (xs i₀).valid).b.toNat := by
  let g : Fin n → ℕ := fun i =>
    (FloatBits.finite (xs i).s (xs i).e (xs i).m (xs i).valid).b.toNat
  have h_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨i₀, _, h_max⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n)) g h_ne
  refine ⟨i₀, ?_, fun j => h_max j (Finset.mem_univ j)⟩
  exact fpMin_eq_of_bit_argmax_nonpos xs hn h_np i₀
    (fun j => h_max j (Finset.mem_univ j))

end Fp
