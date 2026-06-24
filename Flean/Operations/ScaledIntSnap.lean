import Flean.Operations.ScaledInt
import Flean.Operations.ExactIntModP
import Mathlib.Algebra.Order.Round

/-! # The snapping bridge: recovering a precise integer from a noisy `ScaledInt`

The structural shadows (`IsResidue`, `IsResiduePair`, …) live on the **precise pillar**
(`ExactInt`): a residue is brittle, so it cannot ride a growing `err`. But a real modular-arith
net is *computed in floating point* — it lives on the **approximate pillar** (`ScaledInt`), with a
running error bound. This file is the bridge between the two, and the gate is a single threshold.

If a `ScaledInt`'s ideal value is an integer `N` and its accumulated error is below `½`, then the
unique integer within `½` of the actual float is `N`, so **rounding the noisy float recovers `N`
exactly** (`round_eq_of_value_int`). Below the threshold the discrete structure survives the
floating-point noise; above it, the structure is genuinely lost. That `½` is exactly the
**"discretization α"** from the design note (`.claude/notes/exact-int-design.md`): the radius at
which a continuous/metric value snaps back onto the discrete integer lattice.

Once snapped, the recovered integer feeds the whole `IsImage` machinery: its image in *any* target
ring is determined (`snap_image`), and in particular its residue mod `p` is exactly `N mod p`
(`snap_residue`) — "mod-p tolerates error, but only below the ½ threshold." This is the precise
sense in which an *inexact* float computation still pins down a *discrete* structural fact.
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

omit [FloatFormat] in
/-- **Recovery lemma.** A real within `½` of an integer rounds back to exactly that integer. The
`½` is the recoverability threshold — the radius inside which the nearest integer is unique. -/
theorem round_eq_of_abs_sub_lt_half {v : R} {n : ℤ} (h : |v - (n : R)| < 1 / 2) :
    round v = n := by
  rw [abs_sub_lt_iff] at h
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith [h.1, h.2]

namespace ScaledInt

/-- **The snapping bridge.** If a `ScaledInt`'s ideal value is the integer `N` and its accumulated
error is below the `½` recoverability threshold, the *actual float* rounds to exactly `N`. The
noisy approximate-pillar value recovers a precise integer. -/
theorem round_eq_of_value_int (a : ScaledInt R) (N : ℤ)
    (hN : a.value = (N : R)) (hsmall : a.err < 1 / 2) :
    round (a.fp.toVal : R) = N := by
  apply round_eq_of_abs_sub_lt_half
  have h := a.herr
  have hv : (a.m : R) * 2 ^ a.s = (N : R) := hN
  rw [hv] at h
  exact lt_of_le_of_lt h hsmall

/-- Snapping for a scale-`0` value: the ideal is the integer `a.m` itself. -/
theorem round_eq_of_scale_zero (a : ScaledInt R) (hs : a.s = 0) (hsmall : a.err < 1 / 2) :
    round (a.fp.toVal : R) = a.m :=
  a.round_eq_of_value_int a.m
    (by show (a.m : R) * 2 ^ a.s = (a.m : R); rw [hs, zpow_zero, mul_one]) hsmall

/-- **Snapping recovers every structural shadow at once.** The image of the snapped integer in
*any* target ring `S` equals `N`'s image — mirroring `IsImage`'s genericity. mod-p, parity, CRT,
… are all recovered below the threshold, by choosing `S`. -/
theorem snap_image {S : Type*} [CommRing S] (a : ScaledInt R) (N : ℤ)
    (hN : a.value = (N : R)) (hsmall : a.err < 1 / 2) :
    ((round (a.fp.toVal : R) : ℤ) : S) = (N : S) := by
  rw [a.round_eq_of_value_int N hN hsmall]

/-- **mod-p tolerates error below the ½ threshold.** Even though the computation that produced
`a` was inexact (`err > 0`), as long as `err < ½` and the ideal is the integer `N`, the residue
mod `p` of the snapped (rounded) result is exactly the ideal residue `(N : ZMod p)`. Above the
threshold the residue would be lost; below it, it is recovered exactly. This is the discrete
structural fact (`IsResidue`) reduced to the exact case via snapping. -/
theorem snap_residue (a : ScaledInt R) (N : ℤ) (p : ℕ)
    (hN : a.value = (N : R)) (hsmall : a.err < 1 / 2) :
    (round (a.fp.toVal : R) : ZMod p) = (N : ZMod p) :=
  a.snap_image N hN hsmall

end ScaledInt
