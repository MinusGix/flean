import Flean.Operations.LogTaylor
import Flean.Operations.StickyExtract
import Flean.Operations.ExpComputableDefs

/-! # Computable log: definitions and bracket correctness

Core computation definitions for `log(x)` and proof infrastructure.
Uses the generic sticky cell extraction from `StickyExtract.lean`.

## Algorithm

1. **Domain handling**: `log` is defined for positive FP inputs.
   - `x = 1` → exact result `log(1) = 0` (handled at op layer)
   - `x > 1` → compute `log(x)` directly (positive)
   - `0 < x < 1` → compute `log(1/x) = -log(x)` (positive), track sign

2. **Argument reduction** (`logArgRedK`): for `y ≥ 1`, compute `k = ⌊log₂ y⌋`
   so that `y = 2^k · (1+t)` with `t ∈ [0, 1)`.
   Then `log(y) = k · log(2) + log(1+t)`.

3. **Bracket computation** (`logBounds`): at each iteration, compute tighter
   bounds on `log(2)` (via `ln2SeriesSum`) and `log(1+t)` (via alternating
   Taylor series).

4. **Extraction**: `stickyExtractLoop (logBounds ...) 0 (logFuel ...)` identifies
   the sticky cell.
-/

section LogComputable

variable [FloatFormat]

/-! ## Argument reduction -/

/-- Compute `k = ⌊log₂ y⌋` for `y ≥ 1` (given as a rational `p/d` with `p ≥ d`).
Returns `k : ℕ` such that `2^k ≤ y < 2^(k+1)`, i.e., `y / 2^k ∈ [1, 2)`. -/
def logArgRedK (y : ℚ) : ℕ :=
  let p := y.num.natAbs
  let d := y.den
  let n := p / d  -- ⌊y⌋
  if n = 0 then 0 else Nat.log 2 n

/-- Reduced argument `t = y / 2^k - 1` for the log Taylor series.
For `y ≥ 1` and `k = logArgRedK y`, gives `t ∈ [0, 1)`. -/
def logReducedArg (y : ℚ) (k : ℕ) : ℚ :=
  y / (2 : ℚ) ^ k - 1

/-! ## Bounds computation -/

/-- Number of base Taylor terms for log. -/
def logNumTerms : ℕ := FloatFormat.prec.toNat + 10

/-- Generous fuel for the log extraction loop.
Similar structure to `expFuel`, quadratic in the input size. -/
def logFuel (y : ℚ) : ℕ :=
  let ab := y.num.natAbs ^ 2 / y.den + y.num.natAbs + y.den + FloatFormat.prec.toNat + 100
  15 * ab * (Nat.log2 ab + 1) + 200

/-- Compute rational brackets for `log(y)` at precision level `iter`.
Returns `(lower, upper)` such that `lower < log(y) ≤ upper` (approximately).

Strategy: `log(y) = k · log(2) + log(1+t)` where `t = y/2^k - 1`.
- `log(2)` is bracketed by `[ln2_lo, ln2_hi]` from `ln2SeriesSum`
- `log(1+t)` is bracketed by `[taylorLogQ t (2N), taylorLogQ t (2N+1)]`
  using the alternating series property -/
def logBounds (y : ℚ) (k : ℕ) (iter : ℕ) : ℚ × ℚ :=
  let t := logReducedArg y k
  let N_ln2 := Nat.log2 k + 52 + iter * 50
  let s_ln2 := ln2SeriesSum N_ln2
  let ln2_lo := s_ln2
  let ln2_hi := s_ln2 + 1 / 2 ^ N_ln2
  let N := logNumTerms + iter * 10
  let log1t_lo := logLowerBound t N  -- even partial sum (lower bound)
  let log1t_hi := logUpperBound t N  -- odd partial sum (upper bound)
  -- log(y) = k·log(2) + log(1+t)
  -- Lower: k·ln2_lo + log1t_lo  (all terms at their lower bounds)
  -- Upper: k·ln2_hi + log1t_hi  (all terms at their upper bounds)
  (k * ln2_lo + log1t_lo, k * ln2_hi + log1t_hi)

/-! ## Main kernel -/

/-- The `logTarget` function for the `OpRefExecSound` framework.

For `a.toVal = 1`: returns 1 (dummy positive value; the op layer handles this case).
Otherwise: returns `|Real.log(a.toVal)|`.

The dummy value at `x = 1` is needed because `OpRefExecSound` requires positive
values for exact cases, and `log(1) = 0`. The op layer recognizes `x = 1` and
returns floating-point zero directly, bypassing the reference kernel output. -/
noncomputable def logTarget [FloatFormat] (a : FiniteFp) : ℝ :=
  if a.toVal (R := ℚ) = 1 then 1
  else |Real.log (a.toVal (R := ℝ))|

/-- Computable log reference kernel.

For `a.toVal = 1`: returns exact result (dummy, handled at op layer).
For `a.toVal > 1`: computes `log(a.toVal)` via sticky extraction.
For `0 < a.toVal < 1`: computes `log(1/a.toVal) = -log(a.toVal)` via sticky extraction.

The sign of `log(a.toVal)` is tracked separately at the operation layer. -/
def logComputableRun (a : FiniteFp) : OpRefOut :=
  let x : ℚ := a.toVal
  if x = 1 then
    -- log(1) = 0, return dummy exact result (op layer handles this)
    { q := 1, e_base := -1, isExact := true }
  else
    -- Work with y = max(x, 1/x) ≥ 1 so log(y) > 0
    let y := if 1 < x then x else 1 / x
    let k := logArgRedK y
    (stickyExtractLoop (logBounds y k) 0 (logFuel y)).toOpRefOut

instance (priority := 500) : OpRefExec logTarget where
  run := logComputableRun

end LogComputable

/-! ## Smoke tests -/

-- taylorLogQ: log(1+1) = ln(2) ≈ 0.6931...
-- With 20 terms: should be close
#eval taylorLogQ 1 20  -- expect ≈ 0.6931...

-- logArgRedK: for y = 3, ⌊log₂ 3⌋ = 1
#eval logArgRedK 3  -- expect 1

-- logReducedArg: for y = 3, k = 1: t = 3/2 - 1 = 1/2
#eval logReducedArg 3 1  -- expect 1/2

-- logComputableRun: log(1) = 0 (exact case)
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  logComputableRun ⟨false, 0, 1024, by native_decide⟩

-- logComputableRun: log(2) for binary16
-- value 2 = m · 2^(e - prec + 1) = 1024 · 2^(1 - 10) = 1024 · 2^(-9) = 2
#eval
  letI : FloatFormat := FloatFormat.Binary16.toFloatFormat
  logComputableRun ⟨false, 1, 1024, by native_decide⟩
