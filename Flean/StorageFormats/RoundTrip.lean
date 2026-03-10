import Flean.StorageFormats.FromFp
import Flean.StorageFormats.Conversion

/-!
# Round-Trip Properties for StorageFp ↔ FiniteFp

Proves that encoding a value already representable in the target format
and then decoding gives back the original value.

The key property: for any finite `StorageFp v`, decoding it to `FiniteFp`
(via `toFiniteFp`) and re-encoding (via `fromFiniteFp`) recovers `v`.
-/

namespace StorageFp

/-!
## Concrete Round-Trip Verification

Verify round-trip for specific values in each format using `by decide`.
-/

section E4M3_roundtrip

private local instance : FloatFormat := FloatFormat.ofE4M3

-- Zero round-trips
theorem roundtrip_zero_E4M3 :
    fromFiniteFp E4M3 .saturate
      (toFiniteFp (zero E4M3) (by decide) (by decide) (by decide) (zero_isFinite E4M3)) =
    zero E4M3 := by decide

-- One (1.0) round-trips
theorem roundtrip_one_E4M3 :
    fromFiniteFp E4M3 .saturate
      (toFiniteFp (one E4M3) (by decide) (by decide) (by decide) (one_isFinite_E4M3)) =
    one E4M3 := by decide

-- maxFinite round-trips
theorem roundtrip_maxFinite_E4M3 :
    fromFiniteFp E4M3 .saturate
      (toFiniteFp (maxFinite E4M3) (by decide) (by decide) (by decide) (maxFinite_isFinite_E4M3)) =
    maxFinite E4M3 := by decide

-- minPos (smallest subnormal) round-trips
theorem roundtrip_minPos_E4M3 :
    fromFiniteFp E4M3 .saturate
      (toFiniteFp (minPos E4M3) (by decide) (by decide) (by decide) (minPos_isFinite_E4M3)) =
    minPos E4M3 := by decide

-- Negative one round-trips
theorem roundtrip_negOne_E4M3 :
    fromFiniteFp E4M3 .saturate
      (toFiniteFp (ofFields E4M3 true 7 0) (by decide) (by decide) (by decide) (by decide)) =
    ofFields E4M3 true 7 0 := by decide

end E4M3_roundtrip

section E5M2_roundtrip

private local instance : FloatFormat := FloatFormat.ofE5M2

theorem roundtrip_zero_E5M2 :
    fromFiniteFp E5M2 .saturate
      (toFiniteFp (zero E5M2) (by decide) (by decide) (by decide) (zero_isFinite E5M2)) =
    zero E5M2 := by decide

theorem roundtrip_one_E5M2 :
    fromFiniteFp E5M2 .saturate
      (toFiniteFp (one E5M2) (by decide) (by decide) (by decide) (one_isFinite_E5M2)) =
    one E5M2 := by decide

theorem roundtrip_maxFinite_E5M2 :
    fromFiniteFp E5M2 .saturate
      (toFiniteFp (maxFinite E5M2) (by decide) (by decide) (by decide) (maxFinite_isFinite_E5M2)) =
    maxFinite E5M2 := by decide

theorem roundtrip_minPos_E5M2 :
    fromFiniteFp E5M2 .saturate
      (toFiniteFp (minPos E5M2) (by decide) (by decide) (by decide) (minPos_isFinite_E5M2)) =
    minPos E5M2 := by decide

end E5M2_roundtrip

section E3M2_roundtrip

private local instance : FloatFormat := FloatFormat.ofE3M2

theorem roundtrip_zero_E3M2 :
    fromFiniteFp E3M2 .saturate
      (toFiniteFp (zero E3M2) (by decide) (by decide) (by decide) (zero_isFinite E3M2)) =
    zero E3M2 := by decide

theorem roundtrip_one_E3M2 :
    fromFiniteFp E3M2 .saturate
      (toFiniteFp (one E3M2) (by decide) (by decide) (by decide) (one_isFinite_E3M2)) =
    one E3M2 := by decide

theorem roundtrip_maxFinite_E3M2 :
    fromFiniteFp E3M2 .saturate
      (toFiniteFp (maxFinite E3M2) (by decide) (by decide) (by decide) (maxFinite_isFinite_E3M2)) =
    maxFinite E3M2 := by decide

theorem roundtrip_minPos_E3M2 :
    fromFiniteFp E3M2 .saturate
      (toFiniteFp (minPos E3M2) (by decide) (by decide) (by decide) (minPos_isFinite_E3M2)) =
    minPos E3M2 := by decide

end E3M2_roundtrip

section E2M3_roundtrip

private local instance : FloatFormat := FloatFormat.ofE2M3

theorem roundtrip_zero_E2M3 :
    fromFiniteFp E2M3 .saturate
      (toFiniteFp (zero E2M3) (by decide) (by decide) (by decide) (zero_isFinite E2M3)) =
    zero E2M3 := by decide

theorem roundtrip_one_E2M3 :
    fromFiniteFp E2M3 .saturate
      (toFiniteFp (one E2M3) (by decide) (by decide) (by decide) (one_isFinite_E2M3)) =
    one E2M3 := by decide

theorem roundtrip_maxFinite_E2M3 :
    fromFiniteFp E2M3 .saturate
      (toFiniteFp (maxFinite E2M3) (by decide) (by decide) (by decide) (maxFinite_isFinite_E2M3)) =
    maxFinite E2M3 := by decide

theorem roundtrip_minPos_E2M3 :
    fromFiniteFp E2M3 .saturate
      (toFiniteFp (minPos E2M3) (by decide) (by decide) (by decide) (minPos_isFinite_E2M3)) =
    minPos E2M3 := by decide

end E2M3_roundtrip

section E2M1_roundtrip

private local instance : FloatFormat := FloatFormat.ofE2M1

theorem roundtrip_zero_E2M1 :
    fromFiniteFp E2M1 .saturate
      (toFiniteFp (zero E2M1) (by decide) (by decide) (by decide) (zero_isFinite E2M1)) =
    zero E2M1 := by decide

theorem roundtrip_one_E2M1 :
    fromFiniteFp E2M1 .saturate
      (toFiniteFp (one E2M1) (by decide) (by decide) (by decide) (one_isFinite_E2M1)) =
    one E2M1 := by decide

theorem roundtrip_maxFinite_E2M1 :
    fromFiniteFp E2M1 .saturate
      (toFiniteFp (maxFinite E2M1) (by decide) (by decide) (by decide) (maxFinite_isFinite_E2M1)) =
    maxFinite E2M1 := by decide

theorem roundtrip_minPos_E2M1 :
    fromFiniteFp E2M1 .saturate
      (toFiniteFp (minPos E2M1) (by decide) (by decide) (by decide) (minPos_isFinite_E2M1)) =
    minPos E2M1 := by decide

end E2M1_roundtrip

/-!
## Exhaustive Round-Trip Verification

Verify the round-trip property for ALL finite values in each format
by exhaustive enumeration. This provides complete correctness guarantees
for each concrete format without needing general bitvector extensionality.
-/

end StorageFp

-- Fintype instances needed for exhaustive verification via native_decide
instance BitVec.instFintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n))
    ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun ⟨_⟩ => rfl⟩

instance StorageFp.instFintype (f : StorageFormat) : Fintype (StorageFp f) :=
  Fintype.ofEquiv (BitVec f.bitSize) ⟨fun b => ⟨b⟩, fun v => v.bits, fun _ => rfl, fun _ => rfl⟩

namespace StorageFp

section exhaustive

private local instance : FloatFormat := FloatFormat.ofE4M3

/-- Every finite E4M3 value round-trips through toFiniteFp/fromFiniteFp. -/
theorem roundtrip_all_E4M3 :
    ∀ v : StorageFp E4M3, ∀ (h : v.isFinite),
      fromFiniteFp E4M3 .saturate
        (v.toFiniteFp (by decide) (by decide) (by decide) h) = v := by native_decide

end exhaustive

section exhaustive2

private local instance : FloatFormat := FloatFormat.ofE5M2

theorem roundtrip_all_E5M2 :
    ∀ v : StorageFp E5M2, ∀ (h : v.isFinite),
      fromFiniteFp E5M2 .saturate
        (v.toFiniteFp (by decide) (by decide) (by decide) h) = v := by native_decide

end exhaustive2

section exhaustive3

private local instance : FloatFormat := FloatFormat.ofE3M2

theorem roundtrip_all_E3M2 :
    ∀ v : StorageFp E3M2, ∀ (h : v.isFinite),
      fromFiniteFp E3M2 .saturate
        (v.toFiniteFp (by decide) (by decide) (by decide) h) = v := by native_decide

end exhaustive3

section exhaustive4

private local instance : FloatFormat := FloatFormat.ofE2M3

theorem roundtrip_all_E2M3 :
    ∀ v : StorageFp E2M3, ∀ (h : v.isFinite),
      fromFiniteFp E2M3 .saturate
        (v.toFiniteFp (by decide) (by decide) (by decide) h) = v := by native_decide

end exhaustive4

section exhaustive5

private local instance : FloatFormat := FloatFormat.ofE2M1

theorem roundtrip_all_E2M1 :
    ∀ v : StorageFp E2M1, ∀ (h : v.isFinite),
      fromFiniteFp E2M1 .saturate
        (v.toFiniteFp (by decide) (by decide) (by decide) h) = v := by native_decide

end exhaustive5

end StorageFp
