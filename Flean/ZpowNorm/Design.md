# ZpowNorm Tactic — Design Document

## Motivation

Floating-point proofs constantly manipulate expressions of the form `(2 : R) ^ e`
where `e` is an integer exponent. Three operations recur across ~95 sites in 31+ files:

1. **Collapsing/splitting zpow products:** `2^a * 2^b = 2^(a+b)` (or reverse)
2. **Bridging ℕ↔ℤ exponent casts:** `(2:R)^n.toNat = (2:R)^(n:ℤ)`
3. **Proving exponent equalities:** `a + (b - a + 1) = b + 1` via `ring`/`omega`

Currently each instance requires 2–5 tactic calls:
```lean
rw [← zpow_natCast (2 : R), FloatFormat.prec_sub_one_toNat_eq, two_zpow_mul]
congr 1; ring
```

`zpow_norm` would replace these with a single call.

## Scope

### In scope

**Equality goals** where both sides are zpow expressions (base 2, over a generic field R):
```lean
-- Product collapse
(2 : R) ^ a * (2 : R) ^ b = (2 : R) ^ (a + b)

-- Product split (reverse direction)
(2 : R) ^ (a + b) = (2 : R) ^ a * (2 : R) ^ b

-- With scalar: x * 2^a * 2^b = x * 2^(a+b)
x * (2 : R) ^ a * (2 : R) ^ b = x * (2 : R) ^ (a + b)

-- Division: 2^a / 2^b = 2^(a-b)
(2 : R) ^ a / (2 : R) ^ b = (2 : R) ^ (a - b)

-- ℕ→ℤ cast bridge: (2:R)^n.toNat = (2:R)^n (for n : ℤ, n ≥ 0)
(2 : R) ^ FloatFormat.prec.toNat = (2 : R) ^ FloatFormat.prec

-- Combined: cast + collapse
(2 : R) ^ FloatFormat.prec.toNat * (2 : R) ^ (e - prec + 1) = (2 : R) ^ (e + 1)

-- zpow_add_one₀ pattern: 2 * 2^n = 2^(n+1)
(2 : R) * (2 : R) ^ n = (2 : R) ^ (n + 1)
```

**Rewriting in hypotheses** via `zpow_norm at h`.

### Out of scope

- **Inequalities:** `2^a ≤ 2^b` — that's `linearize`'s job
- **Non-power-of-2 bases:** Could generalize later but base 2 covers all current uses
- **Noncommutative rings:** All our types are commutative fields

## Relationship to existing tactics

| Tactic | Domain | Example |
|--------|--------|---------|
| `linearize` | Inequalities between zpow terms | `2^a ≤ 2^b` → `a ≤ b` |
| `bound_calc` | Product bound decomposition | `a*b ≤ c*d` |
| **`zpow_norm`** | Equalities of zpow expressions | `2^a * 2^b = 2^(a+b)` |
| `ring` | Pure ring arithmetic | `a + b = b + a` |

`zpow_norm` fills the gap: `ring` can't handle `zpow`, `simp` doesn't chain
these rewrites reliably, and `linearize`/`bound_calc` handle inequalities, not equalities.

## Algorithm

### Step 1: Normalize both sides to canonical form

Canonical form: `c * (2 : R) ^ E` where:
- `c` is a scalar (possibly 1, possibly a product of non-zpow terms)
- `E` is a single exponent expression

Normalization rules (applied left-to-right):
1. `(2:R)^a * (2:R)^b` → `(2:R)^(a+b)` (via `two_zpow_mul` / `zpow_add₀`)
2. `(2:R)^a / (2:R)^b` → `(2:R)^(a-b)` (via `two_zpow_div` / `zpow_sub₀`)
3. `(2:R)^n.toNat` → `(2:R)^(n:ℤ)` (via `zpow_natCast` + `prec_toNat_eq` etc.)
4. `(2:R) * ...` → `(2:R)^1 * ...` (via `← zpow_one`)
5. `1 * x` → `x`, `x * 1` → `x` (cleanup)

### Step 2: Match normalized forms

After normalization, both sides should have the form `c * 2^E_lhs = c * 2^E_rhs`.
If `c` matches (by `isDefEq`), reduce to `E_lhs = E_rhs`.

### Step 3: Solve exponent equality

Try in order:
1. `rfl` (definitional equality)
2. `ring` (polynomial arithmetic on ℤ)
3. `omega` (linear arithmetic with ℕ↔ℤ casts)
4. `push_cast; ring` (for mixed ℕ/ℤ exponents)

### Implementation approach

Two possible strategies:

**A. Rewrite-based (simpler):**
Apply a `simp` lemma set containing `two_zpow_mul`, `two_zpow_div`, `zpow_natCast`,
`prec_toNat_eq`, `prec_sub_one_toNat_eq`, etc. Then close with `congr 1; ring` or
`congr 1; omega`.

**B. Expr-walking (more robust):**
Walk the Expr tree, collect zpow factors, compute a symbolic exponent sum,
construct a proof via `zpow_add₀` chains. Similar to bound_calc's factor extraction.

Strategy A is simpler and likely sufficient for 90%+ of sites. Start there.

## Syntax

```lean
-- Close an equality goal involving zpow expressions
zpow_norm

-- Normalize zpow in a hypothesis
zpow_norm at h

-- Normalize everywhere
zpow_norm at *
```

## Key lemmas to use

From `Flean/Util.lean`:
- `two_zpow_mul : (2:R)^a * (2:R)^b = (2:R)^(a+b)`
- `two_zpow_div : (2:R)^a / (2:R)^b = (2:R)^(a-b)`
- `mul_two_zpow_right : x * (2:R)^a * (2:R)^b = x * (2:R)^(a+b)`
- `div_two_zpow_mul_two_zpow : x / (2:R)^a * (2:R)^b = x * (2:R)^(b-a)`
- `mul_two_zpow_div_two_zpow : x * (2:R)^a / (2:R)^b = x * (2:R)^(a-b)`

From Mathlib:
- `zpow_add₀ : a ≠ 0 → a^(m+n) = a^m * a^n`
- `zpow_sub₀ : a ≠ 0 → a^(m-n) = a^m / a^n`
- `zpow_natCast : a^(n:ℤ) = a^n` (bridges zpow ↔ npow)
- `zpow_one : a^(1:ℤ) = a`
- `zpow_zero : a^(0:ℤ) = 1`
- `zpow_add_one₀ : a ≠ 0 → a^(n+1) = a^n * a`

From `Flean/FloatFormat.lean`:
- `FloatFormat.prec_toNat_eq : (prec.toNat : ℤ) = prec`
- `FloatFormat.prec_sub_one_toNat_eq : ((prec - 1).toNat : ℤ) = prec - 1`

## Expected impact

~95 sites across 31 files. Most are 2–3 line tactic sequences → 1 line.
Heaviest files: RoundNormal (~15), RoundUp (~12), RoundDown (~10),
RoundIntSigPolicySound (~12), OddInterval (~8).
