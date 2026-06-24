import Flean.Operations.AffineForm

/-! # The generic degree-`d` Taylor-model tower

`AffineForm` (degree 1) and `QuadForm` (degree 2) are the first two rungs of a tower; they share
*everything* about their additive and scaling structure, differing only in the degree of the
polynomial shadow. This file factors that out: a single `PolyForm R d` — a float tracking a
degree-`d` polynomial ideal `∑_{i≤d} cᵢ·xⁱ` — with the degree-generic operations written **once for
all `d`**.

What factors (proved once, for every `d`):
* `value`, the concretization `γ` (`abs_toVal_sub_value_le`), `ofExact`;
* `add` (coefficient-wise, `+` stays degree `d`) and `scaleConst` (scale all coefficients) and
  `neg` — all via the *same* shape-agnostic forward-error transformers (`fpAddFinite_inexact_general`
  etc.).

`AffineForm` ≅ `PolyForm 1` and `QuadForm` ≅ `PolyForm 2` (see `value_one`/`value_two`, which
specialize the generic ideal to `c₀ + c₁·x` and `c₀ + c₁·x + c₂·x²`).

What does *not* factor uniformly is the cross-degree interaction — multiplication raises the degree
(`PolyForm d × PolyForm e → PolyForm (d+e)`, exact) and truncation lowers it (leaking the dropped
high-degree terms). That is the genuine content of the tower (the "× leaks" / "catch the leak"
story), and it is exactly the part that is degree-*changing*; the structure here is the degree-fixed
skeleton it acts on. (Mirrors the discrete side, where `IsImage`'s structure factored but the
cross-domain `.map` carried the real content.)
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float paired with the degree-`d` polynomial ideal `∑_{i≤d} cᵢ·xⁱ` it approximates, with a
deviation bound `err`. The generic rung of the Taylor-model tower. -/
structure PolyForm (R : Type*) [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (d : ℕ) where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- Coefficients `c₀ … c_d`. -/
  c : Fin (d + 1) → R
  /-- The input point. -/
  x : R
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the polynomial ideal. -/
  herr : |(fp.toVal : R) - ∑ i : Fin (d + 1), c i * x ^ (i : ℕ)| ≤ err

namespace PolyForm

variable {d : ℕ}

/-- The polynomial ideal `∑_{i≤d} cᵢ·xⁱ` this approximates. -/
def value (p : PolyForm R d) : R := ∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ)

/-- The form tracks its ideal: the float is within `err` of the polynomial value (γ). -/
theorem abs_toVal_sub_value_le (p : PolyForm R d) :
    |(p.fp.toVal : R) - p.value| ≤ p.err := p.herr

/-- The exact base case: a float realising a polynomial value exactly, with zero error. -/
def ofExact (f : FiniteFp) (c : Fin (d + 1) → R) (x : R)
    (h : (f.toVal : R) = ∑ i : Fin (d + 1), c i * x ^ (i : ℕ)) : PolyForm R d :=
  ⟨f, c, x, 0, by rw [h]; simp⟩

@[simp] theorem ofExact_err (f : FiniteFp) (c : Fin (d + 1) → R) (x : R)
    (h : (f.toVal : R) = ∑ i : Fin (d + 1), c i * x ^ (i : ℕ)) :
    (ofExact f c x h).err = (0 : R) := rfl

/-! ## Recovering the first two rungs -/

/-- `PolyForm 1`'s ideal is the affine `c₀ + c₁·x` — i.e. an `AffineForm`. -/
theorem value_one (p : PolyForm R 1) : p.value = p.c 0 + p.c 1 * p.x := by
  simp [value, Fin.sum_univ_two]

/-- `PolyForm 2`'s ideal is the quadratic `c₀ + c₁·x + c₂·x²` — i.e. a `QuadForm`. -/
theorem value_two (p : PolyForm R 2) :
    p.value = p.c 0 + p.c 1 * p.x + p.c 2 * p.x ^ 2 := by
  simp [value, Fin.sum_univ_three]

/-! ## The degree-generic operations (written once, for every `d`) -/

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Addition** — coefficient-wise; `+` stays degree `d`. One definition for every degree. -/
def add (p q : PolyForm R d) (hx : p.x = q.x)
    (hsum_ne : (p.fp.toVal : R) + q.fp.toVal ≠ 0)
    (hfin : (p.fp + q.fp).isFinite) : PolyForm R d where
  fp := (p.fp + q.fp).toFiniteOr0
  c := p.c + q.c
  x := p.x
  err := (1 + η) * (p.err + q.err) + η * |p.value + q.value|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hgen := fpAddFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (∑ i : Fin (d + 1), (p.c + q.c) i * p.x ^ (i : ℕ)) = p.value + q.value := by
      simp only [value, ← hx, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hval]; exact hgen

@[simp] theorem add_c (p q : PolyForm R d) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).c = p.c + q.c := rfl
@[simp] theorem add_x (p q : PolyForm R d) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).x = p.x := rfl

@[simp] theorem add_value (p q : PolyForm R d) (hx : p.x = q.x) (hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).value = p.value + q.value := by
  simp only [value, add_c, add_x, ← hx, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Scale by a constant float `w`** — scales every coefficient; ideal becomes `w · value`. -/
def scaleConst (p : PolyForm R d) (w : FiniteFp)
    (hprod_ne : (p.fp.toVal : R) * w.toVal ≠ 0)
    (hfin : (p.fp * w).isFinite) : PolyForm R d where
  fp := (p.fp * w).toFiniteOr0
  c := fun i => p.c i * (w.toVal : R)
  x := p.x
  err := η * |p.value * (w.toVal : R)| + (1 + η) * (p.err * |(w.toVal : R)|)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb0 : |(w.toVal : R) - (w.toVal : R)| ≤ 0 := by simp
    have hmul := fpMulFinite_inexact_general p.fp w p.value (w.toVal : R) p.err 0 _
      p.abs_toVal_sub_value_le hb0 hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : (∑ i : Fin (d + 1), (p.c i * (w.toVal : R)) * p.x ^ (i : ℕ))
        = p.value * (w.toVal : R) := by
      simp only [value, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hval]
    calc |((p.fp * w).toFiniteOr0.toVal : R) - p.value * (w.toVal : R)|
        ≤ η * |p.value * (w.toVal : R)|
            + (1 + η) * (|p.value| * 0 + p.err * |(w.toVal : R)| + p.err * 0)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := hmul
      _ = η * |p.value * (w.toVal : R)| + (1 + η) * (p.err * |(w.toVal : R)|)
            + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ) := by ring

@[simp] theorem scaleConst_c (p : PolyForm R d) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).c = fun i => p.c i * (w.toVal : R) := rfl
@[simp] theorem scaleConst_x (p : PolyForm R d) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).x = p.x := rfl

@[simp] theorem scaleConst_value (p : PolyForm R d) (w hprod_ne hfin) :
    (p.scaleConst w hprod_ne hfin).value = p.value * (w.toVal : R) := by
  simp only [value, scaleConst_c, scaleConst_x, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Compose

/-- **Negation** — total and exact; negates every coefficient. Ideal `↦ −value`. -/
def neg (p : PolyForm R d) : PolyForm R d where
  fp := -p.fp
  c := -p.c
  x := p.x
  err := p.err
  herr := by
    have hsneg : (∑ i : Fin (d + 1), (-p.c) i * p.x ^ (i : ℕ))
        = -∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ) := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [FiniteFp.toVal_neg_eq_neg, hsneg,
      show -(p.fp.toVal : R) - -∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ)
        = -((p.fp.toVal : R) - ∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ)) by ring, abs_neg]
    exact p.herr

@[simp] theorem neg_c (p : PolyForm R d) : p.neg.c = -p.c := rfl
@[simp] theorem neg_x (p : PolyForm R d) : p.neg.x = p.x := rfl
@[simp] theorem neg_err (p : PolyForm R d) : p.neg.err = p.err := rfl

@[simp] theorem neg_value (p : PolyForm R d) : p.neg.value = -p.value := by
  have hsneg : (∑ i : Fin (d + 1), (-p.c) i * p.x ^ (i : ℕ))
      = -∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ) := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  simp only [value, neg_c, neg_x, hsneg]

/-! ## The generic leak step: truncate the top degree

Truncation is the *degree-lowering* operation — the part of the tower that genuinely leaks. The
same float is reinterpreted as a lower-degree form, with the dropped top term absorbed into `err`.
Truncating `e < d` iterates this; the affine/quad `mul`s are (an exact degree-raising product, then)
truncation. No FP op happens here — only a reinterpretation — so it needs no rounding typeclasses.
-/

/-- Splitting an ideal off its top coefficient: `value = (low-degree part) + c_top · x^{d+1}`. -/
theorem value_castSucc_split (p : PolyForm R (d + 1)) :
    p.value = (∑ i : Fin (d + 1), p.c (Fin.castSucc i) * p.x ^ (i : ℕ))
      + p.c (Fin.last (d + 1)) * p.x ^ (d + 1) := by
  rw [value, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- **Truncate the top degree** (`d+1 → d`): keep the same float, drop the top coefficient, and
absorb the leaked top term `c_{d+1}·x^{d+1}` into `err`, bounded over `|x| ≤ X` by
`|c_{d+1}|·X^{d+1}`. The generic leak step of the model-order tower. -/
def truncateOne (p : PolyForm R (d + 1)) (X : R) (hX : |p.x| ≤ X) : PolyForm R d where
  fp := p.fp
  c := fun i => p.c (Fin.castSucc i)
  x := p.x
  err := p.err + |p.c (Fin.last (d + 1))| * X ^ (d + 1)
  herr := by
    have hleak : |p.c (Fin.last (d + 1)) * p.x ^ (d + 1)|
        ≤ |p.c (Fin.last (d + 1))| * X ^ (d + 1) := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hX (d + 1)) (abs_nonneg _)
    have hrw : (p.fp.toVal : R) - ∑ i : Fin (d + 1), p.c (Fin.castSucc i) * p.x ^ (i : ℕ)
        = ((p.fp.toVal : R) - p.value) + p.c (Fin.last (d + 1)) * p.x ^ (d + 1) := by
      rw [value_castSucc_split]; ring
    rw [hrw]
    exact (abs_add_le _ _).trans (add_le_add p.abs_toVal_sub_value_le hleak)

@[simp] theorem truncateOne_c (p : PolyForm R (d + 1)) (X hX) :
    (p.truncateOne X hX).c = fun i => p.c (Fin.castSucc i) := rfl
@[simp] theorem truncateOne_x (p : PolyForm R (d + 1)) (X hX) :
    (p.truncateOne X hX).x = p.x := rfl

/-- The truncated form's ideal is the original minus the dropped top term. -/
@[simp] theorem truncateOne_value (p : PolyForm R (d + 1)) (X hX) :
    (p.truncateOne X hX).value = p.value - p.c (Fin.last (d + 1)) * p.x ^ (d + 1) := by
  rw [show (p.truncateOne X hX).value
        = ∑ i : Fin (d + 1), p.c (Fin.castSucc i) * p.x ^ (i : ℕ) from rfl,
    value_castSucc_split]; ring

/-! ## The degree-raising product: the Cauchy product (`PolyForm d × PolyForm e → PolyForm (d+e)`)

Multiplication is the degree-*coupling* cross-operation: the product of a degree-`d` and a degree-`e`
ideal is a *genuine* degree-`(d+e)` polynomial, so it is caught **exactly** (FP rounding only, no
leak, no input bound `X`). This is `QuadForm.ofAffineMul` (degree-2 catches affine²) generalized to
all rungs at once. The coefficients are the **Cauchy product** `r_k = ∑_{i+j=k} cᵢ·c'ⱼ`. -/

variable {e : ℕ}

/-- The Cauchy-product coefficients: `r_k = ∑_{i+j=k} cᵢ·c'ⱼ`. -/
def mulCoeff (c : Fin (d + 1) → R) (c' : Fin (e + 1) → R) (k : Fin (d + e + 1)) : R :=
  ∑ i : Fin (d + 1), ∑ j : Fin (e + 1), if (i : ℕ) + (j : ℕ) = (k : ℕ) then c i * c' j else 0

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The top Cauchy coefficient of two degree-1 forms is the product of the top (slope) coefficients
— the quadratic term of an affine product. -/
theorem mulCoeff_last_two (c c' : Fin 2 → R) : mulCoeff c c' (Fin.last 2) = c 1 * c' 1 := by
  simp [mulCoeff, Fin.sum_univ_two, Fin.last]

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The indicator sum over `k` picks out the single term at `k.val = i+j` (valid since `i+j ≤ d+e`). -/
theorem inner_cauchy (i : Fin (d + 1)) (j : Fin (e + 1)) (a x : R) :
    (∑ k : Fin (d + e + 1), if (i : ℕ) + (j : ℕ) = (k : ℕ) then a * x ^ (k : ℕ) else 0)
      = a * x ^ ((i : ℕ) + (j : ℕ)) := by
  have hlt : (i : ℕ) + (j : ℕ) < d + e + 1 := by have := i.isLt; have := j.isLt; omega
  rw [Fin.sum_univ_eq_sum_range (fun m => if (i : ℕ) + (j : ℕ) = m then a * x ^ m else 0),
    Finset.sum_ite_eq (Finset.range (d + e + 1)) ((i : ℕ) + (j : ℕ)) (fun m => a * x ^ m),
    if_pos (Finset.mem_range.mpr hlt)]

omit [FloatFormat] [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The Cauchy-product value identity.** The product of two polynomial ideals is the degree-`(d+e)`
polynomial with Cauchy-product coefficients — exact, no leak. -/
theorem mulCoeff_value (c : Fin (d + 1) → R) (c' : Fin (e + 1) → R) (x : R) :
    (∑ i : Fin (d + 1), c i * x ^ (i : ℕ)) * (∑ j : Fin (e + 1), c' j * x ^ (j : ℕ))
      = ∑ k : Fin (d + e + 1), mulCoeff c c' k * x ^ (k : ℕ) := by
  have hlhs : (∑ i : Fin (d + 1), c i * x ^ (i : ℕ)) * (∑ j : Fin (e + 1), c' j * x ^ (j : ℕ))
      = ∑ i : Fin (d + 1), ∑ j : Fin (e + 1), c i * c' j * x ^ ((i : ℕ) + (j : ℕ)) := by
    rw [Fintype.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [pow_add]; ring))
  have hrhs : (∑ k : Fin (d + e + 1), mulCoeff c c' k * x ^ (k : ℕ))
      = ∑ i : Fin (d + 1), ∑ j : Fin (e + 1), c i * c' j * x ^ ((i : ℕ) + (j : ℕ)) := by
    simp only [mulCoeff, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => inner_cauchy i j (c i * c' j) x)
  rw [hlhs, hrhs]

section ComposeMul
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Degree-raising multiplication.** The product of a degree-`d` and a degree-`e` form is a
degree-`(d+e)` form whose ideal is *exactly* `value p · value q` (Cauchy-product coefficients), with
only the FP rounding error — no leak, no input bound. The generic "× raises degree exactly" of the
tower, subsuming `QuadForm.ofAffineMul` and every rung. -/
def mul (p : PolyForm R d) (q : PolyForm R e) (hx : p.x = q.x)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : PolyForm R (d + e) where
  fp := (p.fp * q.fp).toFiniteOr0
  c := mulCoeff p.c q.c
  x := p.x
  err := η * |p.value * q.value|
          + (1 + η) * (|p.value| * q.err + p.err * |q.value| + p.err * q.err)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb := fpMulFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hq : (∑ j : Fin (e + 1), q.c j * p.x ^ (j : ℕ)) = q.value := by
      rw [show q.value = ∑ j : Fin (e + 1), q.c j * q.x ^ (j : ℕ) from rfl, hx]
    have hval : (∑ k : Fin (d + e + 1), mulCoeff p.c q.c k * p.x ^ (k : ℕ)) = p.value * q.value := by
      rw [← hq, show p.value = ∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ) from rfl, ← mulCoeff_value]
    rw [hval]; exact hb

@[simp] theorem mul_c (p : PolyForm R d) (q : PolyForm R e) (hx hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).c = mulCoeff p.c q.c := rfl
@[simp] theorem mul_x (p : PolyForm R d) (q : PolyForm R e) (hx hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).x = p.x := rfl

/-- The product form's ideal *is* `value p · value q`, caught exactly (no leak). -/
@[simp] theorem mul_value (p : PolyForm R d) (q : PolyForm R e) (hx : p.x = q.x) (hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).value = p.value * q.value := by
  have hq : (∑ j : Fin (e + 1), q.c j * p.x ^ (j : ℕ)) = q.value := by
    rw [show q.value = ∑ j : Fin (e + 1), q.c j * q.x ^ (j : ℕ) from rfl, hx]
  rw [show (p.mul q hx hprod_ne hfin).value
        = ∑ k : Fin (d + e + 1), mulCoeff p.c q.c k * p.x ^ (k : ℕ) from rfl,
    ← hq, show p.value = ∑ i : Fin (d + 1), p.c i * p.x ^ (i : ℕ) from rfl, ← mulCoeff_value]

/-- **Closing the loop: the affine `mul` leak IS a degree-truncation of the exact product.** For two
degree-1 forms, the *exact* `PolyForm.mul` produces a degree-2 form whose ideal is precisely
`value p · value q`; truncating it back to degree 1 (`truncateOne`) drops *exactly* the quadratic
term `(p.c 1 · q.c 1)·x²` — the product of the slopes. So the fixed-degree affine leak (cf.
`AffineForm.affine_mul_nonlinearity`'s `|a₁a₂|·X²`) is *literally* the projection of the exact
product onto degree 1: the same leaked term, now identified as a truncation, not bounded by analogy.
The leak is degree-projection — the whole continuous thread's thesis, made an equality. -/
theorem mul_truncateOne_value (p q : PolyForm R 1) (hx : p.x = q.x) (hprod_ne hfin) (X : R)
    (hX : |p.x| ≤ X) :
    ((p.mul q hx hprod_ne hfin).truncateOne X hX).value
      = p.value * q.value - mulCoeff p.c q.c (Fin.last (1 + 1)) * p.x ^ (1 + 1) := by
  rw [truncateOne_value, mul_value, mul_c, mul_x]

end ComposeMul

end PolyForm
