import Flean.Operations.AffineFold

/-!
# Jet Horner: Simultaneous Value and Derivative Evaluation

Evaluates a polynomial `p(x)` and its derivative `p'(x)` simultaneously
using a coupled 2D recurrence:

```
(v₀, d₀) = (aₙ, 0)
(vₖ, dₖ) = (x·vₖ₋₁ + aₙ₋ₖ, x·dₖ₋₁ + vₖ₋₁)
```

After `n` steps: `vₙ = p(x)` and `dₙ = p'(x)`.

The state `(v, d)` is a "1-jet" — the polynomial value plus its first derivative.
Each step is an affine map on `R × R`, making this a natural AffineFold instance:
`L(v, d) = (x·v, x·d + v)` with offset `(c, 0)`.

## Key Property

`L` is additive (it's linear), so `jetHornerExact_affine` follows from AffineFold.
The propagation `jetHornerProp` captures how perturbations in the initial jet propagate
through the coupled recurrence — perturbation in `v₀` affects both `v` and `d`.
-/

namespace JetHorner

open AffineFold

variable {R : Type*} [Field R]

/-! ## Exact Evaluation -/

/-- Exact jet Horner evaluation: simultaneously computes value and derivative. -/
def jetHornerExact : List R → R → R → R → R × R
  | [], v, d, _ => (v, d)
  | c :: cs, v, d, x => jetHornerExact cs (x * v + c) (x * d + v) x

/-- Jet Horner's linear map: `L(v, d) = (x·v, x·d + v)`. -/
def jetHornerL (x : R) : R × R → R × R := fun (v, d) => (x * v, x * d + v)

theorem jetHornerL_additive (x : R) :
    ∀ a b, jetHornerL x (a + b) = jetHornerL x a + jetHornerL x b :=
  fun (v₁, d₁) (v₂, d₂) => by
    simp [jetHornerL, Prod.ext_iff]; constructor <;> ring

/-- Jet Horner offsets: coefficient contributes to value, zero to derivative. -/
def jetHornerOffsets (cs : List R) : List (R × R) := cs.map (·, 0)

/-- `affineFold` with `jetHornerL` and `jetHornerOffsets` equals `jetHornerExact`. -/
theorem affineFold_eq_jetHornerExact (cs : List R) (v d x : R) :
    affineFold (jetHornerL x) (jetHornerOffsets cs) (v, d) =
      jetHornerExact cs v d x := by
  induction cs generalizing v d with
  | nil => simp [affineFold, jetHornerOffsets, jetHornerExact]
  | cons c cs ih =>
    simp only [affineFold, jetHornerOffsets, jetHornerExact, jetHornerL, List.map_cons]
    show affineFold _ _ (x * v + c, x * d + v + 0) = _
    rw [add_zero]
    exact ih _ _

/-- **Jet Horner affine property** (from generic AffineFold).

    Perturbing `(v, d)` by `(ev, ed)` shifts the final state by
    `affineProp (jetHornerL x) n (ev, ed)`. -/
theorem jetHornerExact_affine (cs : List R) (v d ev ed x : R) :
    jetHornerExact cs (v + ev) (d + ed) x =
      ((jetHornerExact cs v d x).1 +
        (affineProp (jetHornerL x) cs.length (ev, ed)).1,
       (jetHornerExact cs v d x).2 +
        (affineProp (jetHornerL x) cs.length (ev, ed)).2) := by
  have h := affineFold_affine (jetHornerL x) (jetHornerL_additive x)
    (jetHornerOffsets cs) (v, d) (ev, ed)
  rw [affineFold_eq_jetHornerExact, affineFold_eq_jetHornerExact] at h
  have hlen : (jetHornerOffsets cs).length = cs.length := by simp [jetHornerOffsets]
  rw [hlen] at h
  simp only [Prod.add_def] at h
  have h1 := congr_arg Prod.fst h
  have h2 := congr_arg Prod.snd h
  simp only [] at h1 h2
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1, h2⟩

/-! ## Exact Decomposition -/

/-- **Exact decomposition for jet Horner**: computed + error propagation = exact.

    This is the 2D AffineFold exact decomposition specialized to jet evaluation.
    Both the value error AND the derivative error are captured. -/
theorem jetHorner_exact_decomposition
    (cs errors : List (R × R)) (v d : R) (computed_v computed_d : R) (x : R)
    (hlen : cs.length = errors.length)
    (hcomputed : (computed_v, computed_d) =
      affineFold (jetHornerL x) (List.zipWith (· - ·) cs errors) (v, d)) :
    (computed_v, computed_d) + affineFold (jetHornerL x) errors (0, 0) =
      affineFold (jetHornerL x) cs (v, d) :=
  affineFold_exact_decomposition (jetHornerL x) (jetHornerL_additive x)
    cs errors (v, d) (computed_v, computed_d) hlen hcomputed

/-! ## Derivative Correctness

The second component of `jetHornerExact` computes the formal derivative.
We prove this algebraically via the product rule identity
`d/dx[x·f(x) + c] = f(x) + x·f'(x)`. -/

/-- The formal derivative of a polynomial in Horner form, evaluated at `x`.
    Defined via the jet: `polyDeriv cs init x = (jetHornerExact cs init 0 x).2`. -/
def polyDeriv (cs : List R) (init x : R) : R :=
  (jetHornerExact cs init 0 x).2

/-- The propagation of `(0, d)` through `jetHornerL`: second component is `d * x^n`. -/
private theorem jetHornerProp_zero_d_snd (n : ℕ) (d x : R) :
    (affineProp (jetHornerL x) n (0, d)).2 = d * x ^ n := by
  induction n generalizing d with
  | zero => simp [affineProp]
  | succ n ih => simp only [affineProp, jetHornerL, mul_zero, zero_add]; rw [ih]; ring

theorem jetHorner_deriv_shift (cs : List R) (init d x : R) :
    (jetHornerExact cs init d x).2 = polyDeriv cs init x + d * x ^ cs.length := by
  unfold polyDeriv
  have h := jetHornerExact_affine cs init 0 0 d x
  simp only [add_zero, zero_add] at h
  have h2 := congr_arg Prod.snd h
  simp only at h2
  rw [h2, jetHornerProp_zero_d_snd]

/-- The propagation of `(0, d)` through `jetHornerL`: first component is 0. -/
private theorem jetHornerProp_zero_d_fst (n : ℕ) (d x : R) :
    (affineProp (jetHornerL x) n (0, d)).1 = 0 := by
  induction n generalizing d with
  | zero => simp [affineProp]
  | succ n ih => simp only [affineProp, jetHornerL, mul_zero]; exact ih _

theorem jetHorner_value_indep_of_deriv (cs : List R) (init d x : R) :
    (jetHornerExact cs init d x).1 = (jetHornerExact cs init 0 x).1 := by
  have h := jetHornerExact_affine cs init 0 0 d x
  simp only [add_zero, zero_add] at h
  have h1 := congr_arg Prod.fst h; simp only [] at h1
  rw [h1, jetHornerProp_zero_d_fst, add_zero]

/-- `polyDeriv` of a constant is 0. -/
theorem polyDeriv_nil (init x : R) : polyDeriv [] init x = 0 := by
  simp [polyDeriv, jetHornerExact]

/-- `polyDeriv` step: unfold one level of the recurrence.

    `polyDeriv(c::cs, init, x) = polyDeriv(cs, x·init+c, x) + init · x^{cs.length}`

    The `init · x^m` term comes from the chain rule: the accumulator `x·init + c`
    depends on `x`, contributing `init` to the derivative via `d/da[p] · da/dx`. -/
theorem polyDeriv_cons (c : R) (cs : List R) (init x : R) :
    polyDeriv (c :: cs) init x =
      polyDeriv cs (x * init + c) x + init * x ^ cs.length := by
  unfold polyDeriv
  simp only [jetHornerExact, mul_zero, zero_add]
  exact jetHorner_deriv_shift cs (x * init + c) init x

/-! ## Propagation Formulas for `affineProp (jetHornerL x)`

The matrix power `[[x,0],[1,x]]^n` applied to `(ev, ed)` gives:
- First component: `x^n * ev`
- Second component: `x^n * ed + n * x^{n-1} * ev`

The cross-coupling term `n * x^{n-1} * ev` is the derivative of the value
propagation `x^n * ev`, reflecting the Leibniz rule structure.
These formulas are essential for the jet Horner derivative error bound. -/

variable [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- **Full propagation formula for `affineProp (jetHornerL x)`.**

    `(affineProp L n (ev, ed)).2 = x^n * ed + ↑n * x^{n-1} * ev`

    This is the `(2,·)` entry of the matrix power `[[x,0],[1,x]]^n`
    applied to the vector `(ev, ed)`. -/
theorem affineProp_jetHornerL_snd (n : ℕ) (x ev ed : R) :
    (affineProp (jetHornerL x) n (ev, ed)).2 =
      x ^ n * ed + ↑n * x ^ (n - 1) * ev := by
  induction n generalizing ev ed with
  | zero => simp [affineProp]
  | succ n ih =>
    -- affineProp L (n+1) (ev, ed) = affineProp L n (L(ev, ed))
    --   = affineProp L n (x*ev, x*ed + ev)
    show (affineProp (jetHornerL x) n (jetHornerL x (ev, ed))).2 = _
    simp only [jetHornerL]
    rw [ih (x * ev) (x * ed + ev)]
    cases n with
    | zero => simp
    | succ n => push_cast; ring

/-- Absolute bound on the second component of propagation. -/
theorem affineProp_jetHornerL_snd_abs_le (n : ℕ) (x ev ed : R) :
    |(affineProp (jetHornerL x) n (ev, ed)).2| ≤
      |x| ^ n * |ed| + ↑n * |x| ^ (n - 1) * |ev| := by
  rw [affineProp_jetHornerL_snd]
  calc |x ^ n * ed + ↑n * x ^ (n - 1) * ev|
      ≤ |x ^ n * ed| + |↑n * x ^ (n - 1) * ev| := abs_add_le _ _
    _ = |x| ^ n * |ed| + ↑n * |x| ^ (n - 1) * |ev| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
            abs_of_nonneg (Nat.cast_nonneg (α := R) n)]

/-- **`polyDeriv` is affine in its initial value.**

    Shifting the initial accumulator by `e` shifts the derivative by
    `n * x^{n-1} * e` — the derivative of the value shift `e * x^n`. -/
theorem polyDeriv_affine (cs : List R) (init e x : R) :
    polyDeriv cs (init + e) x =
      polyDeriv cs init x + ↑cs.length * x ^ (cs.length - 1) * e := by
  unfold polyDeriv
  have h := jetHornerExact_affine cs init 0 e 0 x
  simp only [add_zero] at h
  have h2 := congr_arg Prod.snd h
  simp only at h2
  rw [h2, affineProp_jetHornerL_snd]
  ring

omit [FloorRing R] in
/-- `polyDeriv` is nonneg when computed on nonneg inputs. -/
theorem polyDeriv_nonneg (cs : List R) (init x : R)
    (hinit : 0 ≤ init) (hx : 0 ≤ x) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    0 ≤ polyDeriv cs init x := by
  induction cs generalizing init with
  | nil => simp [polyDeriv_nil]
  | cons c cs ih =>
    rw [polyDeriv_cons]
    have hc : 0 ≤ c := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 0 ≤ c' := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    have hinit' : 0 ≤ x * init + c := by positivity
    linarith [ih (x * init + c) hinit' hrest, mul_nonneg hinit (pow_nonneg hx cs.length)]

/-- `polyDeriv` is monotone in the initial value (for nonneg coefficients and x). -/
theorem polyDeriv_mono (cs : List R) (a b x : R)
    (hab : a ≤ b) (hx : 0 ≤ x) :
    polyDeriv cs a x ≤ polyDeriv cs b x := by
  have hb_eq : b = a + (b - a) := by ring
  rw [hb_eq, polyDeriv_affine]
  linarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg' (n := cs.length))
    (pow_nonneg hx (cs.length - 1))) (by linarith : (0 : R) ≤ b - a)]

/-- For nonempty coefficient list, `polyDeriv` is at least `init * x^{cs.length}`.
    This is the chain-rule term from the first unfolding of `polyDeriv_cons`. -/
theorem polyDeriv_ge_init_mul_xpow (c : R) (cs : List R) (init x : R)
    (hinit : 0 ≤ init) (hx : 0 ≤ x) (hc : 0 ≤ c) (hcs : ∀ c' ∈ cs, 0 ≤ c') :
    init * x ^ cs.length ≤ polyDeriv (c :: cs) init x := by
  rw [polyDeriv_cons]
  linarith [polyDeriv_nonneg cs (x * init + c) x (by positivity) hx hcs]

/-! ## Future Work

- **Connection to Mathlib calculus**: For `R = ℝ`, prove
  `HasDerivAt (fun x => hornerPoly cs init x) (polyDeriv cs init x) x`.
  This connects our algebraic `polyDeriv` to Mathlib's analytic `deriv`.
  Proof: induction using `HasDerivAt.mul` + `hasDerivAt_id` for the
  product rule at each step.

- **FP trace + error bound**: Define `JetHornerStep`/`JetHornerTrace` with
  4 fp operations per step (or 2 FMAs). The error propagation is 2D —
  rounding errors in `v` affect future `d` values. The AffineFold gauge
  bounds would give error bounds for BOTH components simultaneously.

- **Higher-order jets**: Generalize from 1-jets `(v, d)` to k-jets
  `(v, d, d², ..., d^k)` for simultaneous evaluation of polynomial + first
  k derivatives. State is `R^{k+1}`, step is a `(k+1)×(k+1)` affine map.
  The AffineFold framework handles this with `S = Fin (k+1) → R`. -/

end JetHorner
