import Flean.Encoding.Quotient

namespace Fp


-- TODO: We should hopefully be able to use the bitvec representation with the solver integrated into lean, but I need to look into that more.
-- TODO: do we really need to require standard exp range? I think we do for the usual bit saving optimization for finite floats. This isn't major, anyway, since I believe all practical floating point formats are standard.
def toBits [FloatFormat] (f : Fp) : FpQuotient :=
  match f with
  | .finite f =>
    -- We don't need the valid proof to construct the bit pattern, though for reasoning we will need to know it is valid
    let ⟨s, e, m, _valid⟩ := f
    let b := FloatBits.finite s e m
    ⟦b⟧
  | .infinite b =>
    ⟦FloatBits.infinite b⟧
  | .NaN =>
    ⟦FloatBits.NaN false (BitVec.ofNat FloatFormat.significandBits 1) (by
      have := FloatFormat.valid_prec
      unfold FloatFormat.significandBits

      intro h
      rw [BitVec.ofNat_eq_ofNat] at h
      have h := (BitVec.toNat_eq _ _).mp h
      repeat rw [BitVec.toNat_ofNat] at h
      rw [Nat.zero_mod, Nat.one_mod_two_pow] at h
      <;> omega
    )⟧

/-! Convert Bits back into a float.-/
def ofBits [FloatFormat] (b : FloatBits) : Fp := by
  let ⟨sign, exponent, significand⟩ := b.toBitsTriple
  sorry


end Fp

def f := @FiniteFp.toRat FloatFormat.Binary32
#eval! f (0 : @FiniteFp FloatFormat.Binary32)
def f' := @Fp.toBits FloatFormat.Binary32
def v := f' (0 : @Fp FloatFormat.Binary32)
-- #eval! @Fp.FpQuotient.representative FloatFormat.Binary32 v FloatFormat.binary32_standard_exp_range
-- #eval! (@toBits FloatFormat.Binary32 (0 : @Fp FloatFormat.Binary32) FloatFormat.binary32_standard_exp_range).representative
