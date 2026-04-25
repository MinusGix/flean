import Flean.StorageFormats.MixedPrecision

/-!
# Concrete quantization instances

Numerical values of `η_sf` and the subnormal constant for practical
mixed-precision pairs.  These just instantiate the parametric quantities
and evaluate them — no new theorems.
-/

namespace StorageFp

/-! ### `η_sf` values in ℚ

`η_sf = 2 ^ (-(manBits + 1)) = 2 ^ (-prec_sf)` (half machine epsilon at
sf's precision):

| sf   | manBits | prec_sf | η_sf            |
|------|---------|---------|-----------------|
| E4M3 | 3       | 4       | 1/16 ≈ 0.0625   |
| E5M2 | 2       | 3       | 1/8  ≈ 0.125    |
| E3M2 | 2       | 3       | 1/8  ≈ 0.125    |
| E2M3 | 3       | 4       | 1/16 ≈ 0.0625   |
| E2M1 | 1       | 2       | 1/4  = 0.25     | -/

theorem η_sf_E4M3 : (StorageFp.η_sf E4M3 : ℚ) = 1 / 16 := by
  show (2 : ℚ) ^ (-((E4M3.manBits : ℤ) + 1)) = 1 / 16
  show (2 : ℚ) ^ (-(4 : ℤ)) = 1 / 16
  norm_num

theorem η_sf_E5M2 : (StorageFp.η_sf E5M2 : ℚ) = 1 / 8 := by
  show (2 : ℚ) ^ (-((E5M2.manBits : ℤ) + 1)) = 1 / 8
  show (2 : ℚ) ^ (-(3 : ℤ)) = 1 / 8
  norm_num

theorem η_sf_E3M2 : (StorageFp.η_sf E3M2 : ℚ) = 1 / 8 := by
  show (2 : ℚ) ^ (-((E3M2.manBits : ℤ) + 1)) = 1 / 8
  show (2 : ℚ) ^ (-(3 : ℤ)) = 1 / 8
  norm_num

theorem η_sf_E2M3 : (StorageFp.η_sf E2M3 : ℚ) = 1 / 16 := by
  show (2 : ℚ) ^ (-((E2M3.manBits : ℤ) + 1)) = 1 / 16
  show (2 : ℚ) ^ (-(4 : ℤ)) = 1 / 16
  norm_num

theorem η_sf_E2M1 : (StorageFp.η_sf E2M1 : ℚ) = 1 / 4 := by
  show (2 : ℚ) ^ (-((E2M1.manBits : ℤ) + 1)) = 1 / 4
  show (2 : ℚ) ^ (-(2 : ℤ)) = 1 / 4
  norm_num

/-! ### Subnormal-constant values in ℚ

`subnormalConst_sf sf = 2 ^ (-bias - manBits)`:

| sf   | bias | manBits | subnormalConst_sf             |
|------|------|---------|-------------------------------|
| E4M3 | 7    | 3       | 2^(-10) = 1/1024              |
| E5M2 | 15   | 2       | 2^(-17) = 1/131072            |
| E3M2 | 3    | 2       | 2^(-5)  = 1/32                |
-/

theorem subnormalConst_sf_E4M3 : (subnormalConst_sf E4M3 : ℚ) = 1 / 1024 := by
  show (2 : ℚ) ^ (-(E4M3.bias : ℤ) - (E4M3.manBits : ℤ)) = 1 / 1024
  show (2 : ℚ) ^ (-(7 : ℤ) - 3) = 1 / 1024
  norm_num

theorem subnormalConst_sf_E3M2 : (subnormalConst_sf E3M2 : ℚ) = 1 / 32 := by
  show (2 : ℚ) ^ (-(E3M2.bias : ℤ) - (E3M2.manBits : ℤ)) = 1 / 32
  show (2 : ℚ) ^ (-(3 : ℤ) - 2) = 1 / 32
  norm_num

/-! ### Relationship to the in-format `FloatFormat.hEps`

The Phase-3 error-bound statements phrase the coefficient as
`@FloatFormat.hEps (sf.toFloatFormat _ _ _) R _`, i.e., the ambient-
format's half-machine-epsilon.  That is definitionally equal to
`η_sf sf`, giving a clean cross-link. -/

theorem hEps_toFloatFormat_E4M3 :
    (@FloatFormat.hEps FloatFormat.ofE4M3 ℚ _ : ℚ) = η_sf E4M3 := by
  show (2 : ℚ) ^ (-(@FloatFormat.prec FloatFormat.ofE4M3 : ℤ)) = η_sf E4M3
  show (2 : ℚ) ^ (-(4 : ℤ)) = η_sf E4M3
  rw [η_sf_E4M3]; norm_num

theorem hEps_toFloatFormat_E5M2 :
    (@FloatFormat.hEps FloatFormat.ofE5M2 ℚ _ : ℚ) = η_sf E5M2 := by
  show (2 : ℚ) ^ (-(@FloatFormat.prec FloatFormat.ofE5M2 : ℤ)) = η_sf E5M2
  show (2 : ℚ) ^ (-(3 : ℤ)) = η_sf E5M2
  rw [η_sf_E5M2]; norm_num

end StorageFp
