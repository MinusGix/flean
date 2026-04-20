import Flean.Basic
import Flean.FloatFormat

/-!
# `FpInterval`: FP-aware interval arithmetic for `IsBoundedRange` propagation

A tiny interval type `{ lo : R; hi : R }` plus three binary/ternary
operations corresponding to the FP primitives `fpAdd` / `fpMul` /
`fpFMA`.  Each op produces an output interval already widened by the
rounding-slack that the primitive introduces.

## Why this exists

Before this file, the propagation lemmas in `BoundedRangePropagate.lean`
stated output bounds either existentially (`∃ lo' hi', ...`) or as raw
expressions like
```
  IsBoundedRange ((lo₁ + lo₂) - (η · max |lo₁+lo₂| |hi₁+hi₂| + sc))
                 ((hi₁ + hi₂) + (η · max |lo₁+lo₂| |hi₁+hi₂| + sc)) xs
```
Both styles grow unreadable on the second or third chained op.  Naming
the output interval via an `FpInterval`-valued function and giving it
operator notation reveals the structure: chained propagation literally
reads as `A ⊞ B ⊠ C` — interval arithmetic over FP.

## Operations

- `⊞` (`FpInterval.fpAdd`): `fpAdd`-compatible, subnormal-tolerant.
- `⊠` (`FpInterval.fpMul`): `fpMul`-compatible, subnormal-tolerant.
- `FMA[A, B, C]` (`FpInterval.fpFMA`): `fpFMA`-compatible, subnormal-tolerant.
- Normal-range companions (`fpAddN`, `fpMulN`, `fpFMAN`) drop the
  `subnormalConst` tail and are used by the normal-range propagation
  lemmas.

## Important caveats

- The notation carries **rounding-slack semantics**.  `A ⊞ B` is NOT
  ordinary interval addition; it widens by `η · max |A.lo+B.lo|
  |A.hi+B.hi| + sc` (the Nearest-mode error bound plus the subnormal
  tail).
- These operations are **non-associative**.  `(A ⊞ B) ⊞ C ≠ A ⊞ (B ⊞ C)`
  in general, because the slack at each stage depends on the partial
  sum's magnitude.  This faithfully mirrors non-associativity of FP
  arithmetic itself.
-/

set_option autoImplicit false

namespace Flean.Tags

variable [FloatFormat]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-! ## The structure -/

/-- `FpInterval R` carries a closed real interval `[lo, hi]` measured
in `R`.  No well-formedness invariant (lo ≤ hi) is enforced — the
propagation lemmas produce correctly-ordered intervals, and callers
who need the invariant can derive it on demand. -/
structure FpInterval (R : Type*) where
  /-- Lower endpoint. -/
  lo : R
  /-- Upper endpoint. -/
  hi : R

namespace FpInterval

/-! ## Scalar helpers -/

/-- Subnormal absolute-rounding constant: `2^(min_exp - prec)`.  The
additive tail absorbing the subnormal-range error in the unified
operations. -/
def subnormalConst : R := (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)

omit [FloorRing R] in
theorem subnormalConst_pos : (0 : R) < (subnormalConst : R) := by
  unfold subnormalConst; positivity

omit [FloorRing R] in
theorem subnormalConst_nn : (0 : R) ≤ (subnormalConst : R) :=
  le_of_lt subnormalConst_pos

/-- Max magnitude of interval endpoints: `max |lo| |hi|`.  Upper bound
on `|x|` for any `x ∈ [lo, hi]` via `abs_le_max_abs_of_le_le`. -/
def maxMag (A : FpInterval R) : R := max |A.lo| |A.hi|

omit [FloatFormat] [FloorRing R] in
theorem maxMag_nn (A : FpInterval R) : (0 : R) ≤ A.maxMag :=
  le_trans (abs_nonneg _) (le_max_left _ _)

/-! ## Addition

`fpAdd`-compatible: output interval surrounds the exact sum
`[A.lo + B.lo, A.hi + B.hi]` by a slack absorbing one nearest-mode
rounding step. -/

/-- Normal-range add: slack `η · M` where `M = max |lo_sum| |hi_sum|`. -/
def fpAddN (A B : FpInterval R) : FpInterval R :=
  let M : R := max |A.lo + B.lo| |A.hi + B.hi|
  let slack : R := (η : R) * M
  ⟨(A.lo + B.lo) - slack, (A.hi + B.hi) + slack⟩

/-- Unified (subnormal-tolerant) add: slack `η · M + sc`. -/
def fpAdd (A B : FpInterval R) : FpInterval R :=
  let M : R := max |A.lo + B.lo| |A.hi + B.hi|
  let slack : R := (η : R) * M + subnormalConst
  ⟨(A.lo + B.lo) - slack, (A.hi + B.hi) + slack⟩

/-! ## Multiplication

Symmetric-around-0 bounds: mixed-sign products have no natural one-sided
relation to input endpoints. -/

/-- Normal-range mul: `|·| ≤ (1+η) · maxMag A · maxMag B`. -/
def fpMulN (A B : FpInterval R) : FpInterval R :=
  let bound : R := (1 + (η : R)) * (A.maxMag * B.maxMag)
  ⟨-bound, bound⟩

/-- Unified (subnormal-tolerant) mul: `|·| ≤ (1+η) · maxMag A · maxMag B + sc`. -/
def fpMul (A B : FpInterval R) : FpInterval R :=
  let bound : R := (1 + (η : R)) * (A.maxMag * B.maxMag) + subnormalConst
  ⟨-bound, bound⟩

/-! ## Fused multiply-add

Single rounding step over exact `a·b + c`.  Worst-case magnitude
`M := maxMag A · maxMag B + maxMag C`. -/

/-- Normal-range FMA: `|·| ≤ (1+η) · M`. -/
def fpFMAN (A B C : FpInterval R) : FpInterval R :=
  let M : R := A.maxMag * B.maxMag + C.maxMag
  let bound : R := (1 + (η : R)) * M
  ⟨-bound, bound⟩

/-- Unified (subnormal-tolerant) FMA: `|·| ≤ (1+η) · M + sc`. -/
def fpFMA (A B C : FpInterval R) : FpInterval R :=
  let M : R := A.maxMag * B.maxMag + C.maxMag
  let bound : R := (1 + (η : R)) * M + subnormalConst
  ⟨-bound, bound⟩

end FpInterval

/-! ## Notation

Scoped to `Flean.Tags`.  `⊞` / `⊠` denote the subnormal-tolerant
unified operations — the common case.  For normal-range variants,
call `FpInterval.fpAddN` etc. explicitly. -/

@[inherit_doc FpInterval.fpAdd]
scoped infixl:65 " ⊞ " => FpInterval.fpAdd

@[inherit_doc FpInterval.fpMul]
scoped infixl:70 " ⊠ " => FpInterval.fpMul

end Flean.Tags
