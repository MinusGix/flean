# Floating-Point Rounding: Algorithms and Analysis

## Table of Contents
1. [Introduction](#introduction)
2. [Mathematical Foundation](#mathematical-foundation)
3. [IEEE 754 Rounding Modes](#ieee-754-rounding-modes)
4. [Algorithmic Implementation](#algorithmic-implementation)
5. [Edge Cases and Special Values](#edge-cases-and-special-values)
6. [Properties and Invariants](#properties-and-invariants)
7. [Implementation Strategy](#implementation-strategy)

## Introduction

Floating-point rounding is the process of mapping a real number to the nearest representable floating-point value. This is necessary because floating-point formats have finite precision and cannot exactly represent all real numbers.

### Key Concepts

- **Representable Values**: In a floating-point format with precision `p` and exponent range `[emin, emax]`, representable values are:
  - Zero: ±0
  - Normal numbers: ±m × 2^e where 2^(p-1) ≤ m < 2^p and emin ≤ e ≤ emax
  - Subnormal numbers: ±m × 2^emin where 0 < m < 2^(p-1)
  - Special values: ±∞, NaN

- **Rounding Function**: A function `rnd: ℝ → Fp` that maps real numbers to floating-point values

- **Exactness**: A value is exactly representable if `rnd(x) = x`

## Mathematical Foundation

### Floating-Point Grid

For a given exponent `e`, the representable values form a grid with spacing `ulp = 2^(e-p+1)`. Between consecutive powers of 2, the grid spacing doubles.

```
Normal range for exponent e:
[2^e, 2^(e+1)) with grid points at: 2^e, 2^e + 2^(e-p+1), 2^e + 2×2^(e-p+1), ...
```

### Nearest Neighbors

For any real number `x`, we can identify:
- `x⁻`: The largest representable value ≤ x (predecessor)
- `x⁺`: The smallest representable value ≥ x (successor)

If `x` is exactly representable, then `x⁻ = x = x⁺`.

### Midpoints

A midpoint occurs when `x` is exactly halfway between two consecutive representable values:
```
x = (x⁻ + x⁺) / 2
```

## IEEE 754 Rounding Modes

IEEE 754 defines five rounding modes, each with specific behavior:

### 1. Round to Nearest, Ties to Even (RNE)
- **Default mode** in most systems
- Rounds to the nearest representable value
- Ties (midpoints) round to the even significand
- Minimizes bias in repeated operations

```
Algorithm:
if x is exactly representable:
    return x
else if x < (x⁻ + x⁺) / 2:
    return x⁻
else if x > (x⁻ + x⁺) / 2:
    return x⁺
else:  // x is a midpoint
    if x⁻ has even significand:
        return x⁻
    else:
        return x⁺
```

### 2. Round to Nearest, Ties Away from Zero (RNA)
- Rounds to the nearest representable value
- Ties round away from zero (magnitude increases)

```
Algorithm:
if x is exactly representable:
    return x
else if x < (x⁻ + x⁺) / 2:
    return x⁻
else if x > (x⁻ + x⁺) / 2:
    return x⁺
else:  // x is a midpoint
    if x > 0:
        return x⁺
    else:
        return x⁻
```

### 3. Round Toward Zero (RZ)
- Always rounds toward zero (truncation)
- Magnitude never increases

```
Algorithm:
if x is exactly representable:
    return x
else if x > 0:
    return x⁻
else:  // x < 0
    return x⁺
```

### 4. Round Toward Positive Infinity (RP)
- Always rounds up (ceiling function)

```
Algorithm:
if x is exactly representable:
    return x
else:
    return x⁺
```

### 5. Round Toward Negative Infinity (RN)
- Always rounds down (floor function)

```
Algorithm:
if x is exactly representable:
    return x
else:
    return x⁻
```

## Algorithmic Implementation

### Core Algorithm Structure

The general rounding algorithm follows these steps:

1. **Handle special cases**:
   - If x = 0, return ±0 (preserving sign)
   - If |x| < smallest_subnormal/2, handle underflow
   - If |x| > largest_finite, handle overflow

2. **Determine the floating-point interval**:
   - Find exponent: `e = floor(log₂|x|)`
   - Adjust for subnormal range if needed

3. **Compute the two nearest values**:
   - Calculate `x⁻` and `x⁺`
   - Determine if x is exactly representable

4. **Apply rounding rule**:
   - Based on the rounding mode and position of x

### Detailed Algorithm for General Rounding

```
function round(x: Real, mode: RoundingMode) -> Fp:
    // Step 1: Handle zero
    if x = 0:
        return Fp.zero(sign(x))
    
    // Step 2: Extract sign and work with absolute value
    s = sign(x)
    x_abs = |x|
    
    // Step 3: Handle underflow cases
    if x_abs < smallest_pos_subnormal / 2:
        return handleUnderflow(x, mode)
    
    // Step 4: Handle overflow cases
    if x_abs > overflow_threshold(mode):
        return handleOverflow(x, mode)
    
    // Step 5: Determine exponent
    e = floor(log₂(x_abs))
    
    // Step 6: Handle subnormal range
    if e < min_exp:
        return roundSubnormal(x, mode)
    
    // Step 7: Normal range rounding
    return roundNormal(x, e, mode)
```

### Efficient Computation of Neighbors

For a value `x` with exponent `e`:

```
function computeNeighbors(x_abs: Real, e: Int) -> (Fp, Fp):
    ulp = 2^(e - prec + 1)
    
    // Normalized significand in [1, 2)
    m = x_abs / 2^e
    
    // Number of ULPs from 2^e
    k = floor((m - 1) / (ulp / 2^e))
    
    x_minus = 2^e + k * ulp
    x_plus = x_minus + ulp
    
    return (x_minus, x_plus)
```

### Tie Detection

Detecting ties (midpoints) efficiently:

```
function isTie(x: Real, x_minus: Fp, x_plus: Fp) -> Bool:
    midpoint = (x_minus + x_plus) / 2
    return x = midpoint
```

For exact arithmetic, we can also check:
```
function isTie(x_abs: Real, e: Int) -> Bool:
    ulp = 2^(e - prec + 1)
    m = x_abs / 2^e
    fractional_ulps = (m - 1) / (ulp / 2^e)
    return fractional_ulps - floor(fractional_ulps) = 0.5
```

## Edge Cases and Special Values

### 1. Underflow (Near Zero)

When `|x| < smallest_pos_subnormal`:
- RNE, RNA: Round to 0 if `|x| < smallest_pos_subnormal/2`, else to `smallest_pos_subnormal`
- RZ: Always round to 0
- RP: Round positive values to `smallest_pos_subnormal`, negative to 0
- RN: Round positive values to 0, negative to `-smallest_pos_subnormal`

### 2. Overflow (Large Magnitudes)

Overflow thresholds vary by mode:
- RNE, RNA: `|x| ≥ (2 - 2^(1-prec)/2) × 2^max_exp`
- RZ: `|x| > largest_finite`
- RP (for x > 0), RN (for x < 0): `|x| > largest_finite`

Results:
- Within threshold: Round to `largest_finite`
- Beyond threshold: Round to `infinity`

### 3. Subnormal Range

In the subnormal range (`smallest_pos_subnormal ≤ |x| < 2^min_exp`):
- Grid spacing is constant: `2^(min_exp - prec + 1)`
- No implicit leading bit
- Gradual underflow provides better numerical properties

### 4. Exact Representations

Values exactly representable include:
- Small integers: |n| < 2^prec
- Powers of 2 within range: 2^k for min_exp ≤ k ≤ max_exp
- Certain rational numbers with power-of-2 denominators

## Properties and Invariants

### Monotonicity
For all rounding modes: if `x ≤ y`, then `rnd(x) ≤ rnd(y)`

### Sign Preservation
- RNE, RNA, RZ: `sign(rnd(x)) = sign(x)` (except for zero)
- RP, RN: May change sign near zero

### Rounding Error Bounds
- RNE, RNA: `|rnd(x) - x| ≤ ulp(x) / 2`
- Directed modes: `|rnd(x) - x| < ulp(x)`

### Exact Rounding
If `x` is exactly representable, all modes return `x`

### Special Value Handling
- `rnd(±∞) = ±∞` for all modes
- `rnd(NaN) = NaN` for all modes

### Tie-Breaking Properties
- RNE: Statistically unbiased for random ties
- RNA: Slight positive bias for positive values

## Implementation Strategy

### 1. Core Functions to Implement

```lean
-- Find the two nearest floating-point values
def findNeighbors (x : ℝ) : (Fp × Fp)

-- Check if a value is exactly representable
def isExact (x : ℝ) : Bool

-- Check if a value is a tie (midpoint)
def isTie (x : ℝ) : Bool

-- Core rounding for each mode
def roundToNearestTiesToEven (x : ℝ) : Fp
def roundToNearestTiesAway (x : ℝ) : Fp
def roundTowardZero (x : ℝ) : Fp
def roundTowardPositive (x : ℝ) : Fp
def roundTowardNegative (x : ℝ) : Fp
```

### 2. Properties to Prove

```lean
-- Correctness: Result is a valid floating-point number
theorem round_valid (x : ℝ) (mode : RoundingMode) : 
  isValidFp (round mode x)

-- Exactness: Exact values are preserved
theorem round_exact (x : ℝ) (mode : RoundingMode) : 
  isExact x → round mode x = x

-- Monotonicity
theorem round_monotone (x y : ℝ) (mode : RoundingMode) :
  x ≤ y → round mode x ≤ round mode y

-- Error bounds
theorem round_error_bound (x : ℝ) :
  |roundNearestTiesToEven x - x| ≤ ulp x / 2

-- Tie handling
theorem ties_to_even_is_even (x : ℝ) :
  isTie x → isEven (significand (roundNearestTiesToEven x))
```

### 3. Optimization Opportunities

- Use bit manipulation for power-of-2 operations
- Precompute common values (thresholds, special ULPs)
- Special-case handling for common formats (binary32, binary64)
- Leverage the fact that most operations are in normal range

### 4. Testing Strategy

- Exhaustive testing for small formats (e.g., 8-bit toy format)
- Boundary value testing (near special thresholds)
- Tie cases for nearest modes
- Sign symmetry verification
- Comparison with reference implementations

## Conclusion

Floating-point rounding is a fundamental operation that requires careful handling of numerous edge cases. The algorithms presented here provide a complete framework for implementing IEEE 754-compliant rounding with formal verification capabilities. The key insights are:

1. All rounding modes can be expressed in terms of finding nearest neighbors
2. Special value handling must be explicit and correct
3. Tie-breaking rules distinguish the nearest modes
4. Monotonicity and error bounds are critical properties
5. The subnormal range requires special attention

This framework provides a solid foundation for both efficient implementation and formal verification of floating-point rounding operations.