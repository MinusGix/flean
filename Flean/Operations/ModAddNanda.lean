import Flean.Operations.ModAddNanda.Packed
import Flean.Operations.ModAddNanda.Embed
import Flean.Operations.ModAddNanda.Attn
import Flean.Operations.ModAddNanda.Mlp

/-! # Nanda's grokked modular-addition transformer, ingested bit-exactly

The tensors under `Flean.ModAddNanda.Weights` are the **actual learned parameters** of the
mainline grokked transformer from Nanda et al., *Progress measures for grokking via mechanistic
interpretability* (2023): the `full_run_data.pth` checkpoint (seed 0, final saved epoch 49900),
trained on `(a + b) mod 113`.

Architecture (from the checkpoint's config): `p = 113`, one transformer block, `d_model = 128`,
4 attention heads of dimension 32, ReLU MLP of width 512, no LayerNorm, vocabulary `0,…,112, '='`
(114 tokens), context `[a, b, '=']` of length 3, unembedding read at the final position.

What is certified here, entirely inside the kernel (`decide`), with no floating-point trust
boundary:

* **Bit-exactness** — every stored 32-bit word decodes to a `FiniteFp` that re-encodes to the
  same word (`PackedMatrix.value_toBits`); the Lean values *are* the checkpoint, not an
  approximation of it.
* **Well-formedness** — all 226,816 learned parameters are finite Binary32 values (no NaN or
  infinity anywhere in the checkpoint).
* **Magnitude bounds** — uniform per-tensor bounds (`≤ 2⁻¹` down to `≤ 2⁻⁵`, below), the raw
  material for forward-error analysis of the network's arithmetic.

The empirical context (measured, not yet proved): this checkpoint scores 100% on all `113² =
12769` input pairs with minimum logit margin `≈ 9.605` (mean `≈ 17.1`), and its embedding
concentrates ≈94% of its non-DC Fourier power on the five frequencies `{14, 35, 41, 42, 52}`.
The next layers on top of this artifact are the extensional forward-pass certificate and the
gauge-invariant cyclic-representation certificate (see `docs/modadd_clock_representation.md`).
-/

set_option autoImplicit false

namespace Flean.ModAddNanda

private local instance binary32Std : StdFloatFormat := FloatFormat.Binary32

open Weights

/-- Total learned parameter count of the ingested checkpoint (the fixed causal mask is not a
learned parameter and is not stored). -/
theorem paramCount :
    (128 * 114 + 3 * 128 + 128 * 114)          -- embed, positional, unembed
      + 4 * (128 * 128)                        -- attention K, Q, V, O
      + (512 * 128 + 512 + 128 * 512 + 128)    -- MLP weights and biases
      = 226816 := by norm_num

/-! ## Per-tensor magnitude bounds

Each bound is read off the packed certificate; the exponent arithmetic is discharged by `decide`.
-/

/-- Every token-embedding entry has magnitude at most `2⁻¹`. -/
theorem wE_abs_le (i : Fin 128) (j : Fin 114) :
    |((wE.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-1 : ℤ) :=
  wE.abs_value_le' (-1) (by decide) i j

/-- Every positional-embedding entry has magnitude at most `2⁻¹`. -/
theorem wPos_abs_le (i : Fin 3) (j : Fin 128) :
    |((wPos.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-1 : ℤ) :=
  wPos.abs_value_le' (-1) (by decide) i j

/-- Every unembedding entry has magnitude at most `2⁻¹`. -/
theorem wU_abs_le (i : Fin 128) (j : Fin 114) :
    |((wU.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-1 : ℤ) :=
  wU.abs_value_le' (-1) (by decide) i j

/-- Every attention key weight has magnitude at most `2⁻³`. -/
theorem wK_abs_le (i : Fin 128) (j : Fin 128) :
    |((wK.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-3 : ℤ) :=
  wK.abs_value_le' (-3) (by decide) i j

/-- Every attention query weight has magnitude at most `2⁻⁴`. -/
theorem wQ_abs_le (i : Fin 128) (j : Fin 128) :
    |((wQ.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-4 : ℤ) :=
  wQ.abs_value_le' (-4) (by decide) i j

/-- Every attention value weight has magnitude at most `2⁻¹`. -/
theorem wV_abs_le (i : Fin 128) (j : Fin 128) :
    |((wV.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-1 : ℤ) :=
  wV.abs_value_le' (-1) (by decide) i j

/-- Every attention output-projection weight has magnitude at most `2⁻¹`. -/
theorem wO_abs_le (i : Fin 128) (j : Fin 128) :
    |((wO.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-1 : ℤ) :=
  wO.abs_value_le' (-1) (by decide) i j

/-- Every MLP input weight has magnitude at most `2⁻²`. -/
theorem wIn_abs_le (i : Fin 512) (j : Fin 128) :
    |((wIn.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-2 : ℤ) :=
  wIn.abs_value_le' (-2) (by decide) i j

/-- Every MLP input bias has magnitude at most `2⁻³`. -/
theorem bIn_abs_le (i : Fin 1) (j : Fin 512) :
    |((bIn.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-3 : ℤ) :=
  bIn.abs_value_le' (-3) (by decide) i j

/-- Every MLP output weight has magnitude at most `2⁻²`. -/
theorem wOut_abs_le (i : Fin 128) (j : Fin 512) :
    |((wOut.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-2 : ℤ) :=
  wOut.abs_value_le' (-2) (by decide) i j

/-- Every MLP output bias has magnitude at most `2⁻⁵`. -/
theorem bOut_abs_le (i : Fin 1) (j : Fin 128) :
    |((bOut.value i j).toVal : ℝ)| ≤ (2 : ℝ) ^ (-5 : ℤ) :=
  bOut.abs_value_le' (-5) (by decide) i j

end Flean.ModAddNanda
