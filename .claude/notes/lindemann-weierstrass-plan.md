# Plan: Prove irrationality of exp at rational points (Lindemann-Weierstrass algebraic part)

## Context
Two cell agreement sorries remain in `ExpComputable.lean`. They require `⌊lower·2^s⌋ = ⌊upper·2^s⌋`, which needs `exp(x) ≠ k/2^s` for any integer k. This follows from **irrationality of exp at nonzero rationals**, which in turn follows from the Lindemann-Weierstrass theorem. Mathlib has the **analytical part** (`exp_polynomial_approx` in `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`) but NOT the algebraic part. We formalize the algebraic part.

## Target theorem
```lean
theorem irrational_exp_rat (q : ℚ) (hq : q ≠ 0) : Irrational (Real.exp (q : ℝ))
```

## Proof strategy

For `q = a/b` with `b > 0`, `a ≠ 0`:

1. **Construct** `f := C b * X - C a : ℤ[X]` where `a = q.num`, `b = (q.den : ℤ)`.
   - `f.eval 0 = -a ≠ 0`
   - `(q : ℂ) ∈ f.aroots ℂ` (since `aeval (q : ℂ) f = b·q - a = 0`)

2. **Apply** `exp_polynomial_approx f hf0` to get constant `c` and, for each large prime `p`:
   - `n_p : ℤ` with `¬(p : ℤ) ∣ n_p`
   - `gp : ℤ[X]` with `gp.natDegree ≤ p - 1`
   - Bound: `‖n_p • exp(q : ℂ) - p • aeval (q : ℂ) gp‖ ≤ c^p / (p-1)!`

3. **Assume for contradiction** `exp(q : ℝ) = P/Q` with `Q > 0`, `P, Q : ℤ`.

4. **Clear denominators**: multiply bound by `|Q| · |b|^(p-1)`:
   - `aeval (q : ℂ) gp = aeval (a/b : ℂ) gp`. Since `gp.natDegree ≤ p-1`, we have `b^(p-1) · aeval (a/b) gp ∈ ℤ` (standard: clearing denominators of a polynomial evaluated at a/b).
   - LHS becomes `|n_p · P · b^(p-1) - p · Q · M_p|` where `M_p ∈ ℤ`
   - RHS becomes `|Q| · |b|^(p-1) · c^p / (p-1)!`

5. **For large p**, RHS < 1 (since `|b|^p · c^p / (p-1)! → 0`), so the integer LHS = 0.

6. **Divisibility contradiction**: `n_p · P · b^(p-1) = p · Q · M_p` means `p ∣ n_p · P · b^(p-1)`. Since `p ∤ n_p` (given), and for `p > |b|` we have `p ∤ b^(p-1)`, and for `p > |P|` we have `p ∤ P` (if `exp(q) = 0` that's immediate contradiction since `exp > 0`). So `p ∤ n_p · P · b^(p-1)` by `Prime.not_dvd_mul`. But `p | p · Q · M_p`. Contradiction.

## File structure

**New file**: `Flean/NumberTheory/IrrationalExp.lean`

### Helper lemmas needed

1. **`intPoly_aeval_rat_clear_denom`**: For `g : ℤ[X]` with `g.natDegree ≤ d` and `q = a/b`:
   Define `M_p := Σ i, gp.coeff i * a^i * b^(p-1-i)` and show `b^(p-1) * aeval (a/b : ℂ) gp = M_p`.

2. **`factorial_dominates_exp`**: `∀ c : ℝ, ∀ᶠ n in atTop, c^n / (n-1)! < 1`. From `tendsto_pow_div_factorial_atTop` in mathlib.

3. **`prime_not_dvd_of_abs_lt`**: If `p : ℕ` is prime and `0 < |n| < p` then `¬(p : ℤ) ∣ n`. From `Nat.Prime.not_dvd_of_lt`.

### Step-by-step implementation

**Step 1**: Create file with imports and the polynomial setup lemmas
- `exp_rat_poly`: construct `f = C (q.den : ℤ) * X - C q.num`
- `exp_rat_poly_eval_zero`: `f.eval 0 = -q.num`
- `exp_rat_poly_root`: `(q : ℂ) ∈ f.aroots ℂ`

**Step 2**: Clearing denominators lemma
- For `g : ℤ[X]` with `natDegree ≤ d`, `b ≠ 0`:
  `(b : K)^d * aeval (a/b : K) g` is an integer

**Step 3**: The factorial-dominates-exponential extraction
- Extract from `tendsto_pow_div_factorial_atTop`: for any `c : ℝ`, `∃ N, ∀ n ≥ N, |c|^n / n! < ε`

**Step 4**: Main proof assembling everything

**Step 5**: (After IrrationalExp is done) Use in ExpComputable.lean to close both cell agreement sorries

## Key mathlib lemmas to use

- `exp_polynomial_approx` — the analytical heart
- `mem_aroots` / `mem_aroots'` — root membership
- `irrational_iff_ne_rational` — characterize Irrational
- `tendsto_pow_div_factorial_atTop` — c^n/n! → 0
- `Int.Prime.dvd_mul` / `Int.Prime.dvd_pow'` — prime divisibility in ℤ
- `norm_zsmul`, `nsmul_eq_mul`, `zsmul_eq_mul` — norm/smul interaction
- `Complex.ofReal_exp` — bridge `Real.exp` to `Complex.exp`
