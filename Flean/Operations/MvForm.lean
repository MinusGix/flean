import Flean.Operations.AffineForm
import Mathlib.Algebra.MvPolynomial.Eval

/-! # The general multivariate Taylor model — the top of the continuous hierarchy

`AffineForm`/`QuadForm` (degree 1, 2, one input), `AffineFormVec` (degree 1, many inputs), and the
generic `PolyForm` (degree `d`, one input) are all *fixed-degree* models — and the price of fixing
the degree is the **leak**: `×` produces higher-degree terms the model cannot hold, so they are
dumped into `err` (bounded only with an input box).

This file removes the degree restriction entirely. An `MvForm R n` carries, as its ideal, a genuine
**multivariate polynomial** `P : MvPolynomial (Fin n) R` over `n` inputs, with `|fp.toVal − eval x P|
≤ err`. Because `MvPolynomial.eval x` is a **ring homomorphism**, addition and multiplication of the
ideals are just `P + Q` and `P · Q` — and they are **both exact** (only the FP rounding enters
`err`): no leak, no input bound `X`. Polynomials are closed under `+` and `×`, so an unbounded-degree
model never has to truncate.

The punchline of the whole continuous thread: **the leak was never intrinsic to multiplication — it
was an artifact of fixing the degree.** `AffineForm`/`QuadForm`/`AffineFormVec` are `MvForm`
restricted to a bounded total degree; the leak is exactly the cost of projecting `MvForm.mul`'s
result back down to that degree. Carry the full polynomial and `×` is as exact as `+`.

(Ops are `noncomputable` — `MvPolynomial`'s ring structure is — but this is a *specification* domain:
the content is the proofs, not execution.)
-/

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A float paired with a multivariate-polynomial ideal `P` over `n` inputs and an input point `x`,
within `err`. The most general continuous (Taylor-model) domain: arbitrary multivariate polynomial,
all ops exact. -/
structure MvForm (R : Type*) [FloatFormat] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : ℕ) where
  /-- The actual float value. -/
  fp : FiniteFp
  /-- The multivariate-polynomial ideal. -/
  P : MvPolynomial (Fin n) R
  /-- The input point. -/
  x : Fin n → R
  /-- Running error bound. -/
  err : R
  /-- The float is within `err` of the polynomial evaluated at the input. -/
  herr : |(fp.toVal : R) - MvPolynomial.eval x P| ≤ err

namespace MvForm

variable {n : ℕ}

/-- The ideal value `eval x P`. -/
noncomputable def value (p : MvForm R n) : R := MvPolynomial.eval p.x p.P

/-- The form tracks its ideal (γ). -/
theorem abs_toVal_sub_value_le (p : MvForm R n) :
    |(p.fp.toVal : R) - p.value| ≤ p.err := p.herr

/-- The exact base case. -/
noncomputable def ofExact (f : FiniteFp) (P : MvPolynomial (Fin n) R) (x : Fin n → R)
    (h : (f.toVal : R) = MvPolynomial.eval x P) : MvForm R n :=
  ⟨f, P, x, 0, by rw [h]; simp⟩

@[simp] theorem ofExact_err (f : FiniteFp) (P : MvPolynomial (Fin n) R) (x : Fin n → R)
    (h : (f.toVal : R) = MvPolynomial.eval x P) : (ofExact f P x h).err = (0 : R) := rfl

section Compose
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R]
  [RModeNearest R] [RModeConj R] [RModeZero R]

/-- **Addition** — ideals add (`P + Q`); exact on the shadow (`eval` is a ring hom). -/
noncomputable def add (p q : MvForm R n) (hx : p.x = q.x)
    (hsum_ne : (p.fp.toVal : R) + q.fp.toVal ≠ 0)
    (hfin : (p.fp + q.fp).isFinite) : MvForm R n where
  fp := (p.fp + q.fp).toFiniteOr0
  P := p.P + q.P
  x := p.x
  err := (1 + η) * (p.err + q.err) + η * |p.value + q.value|
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hgen := fpAddFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hsum_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : MvPolynomial.eval p.x (p.P + q.P) = p.value + q.value := by
      simp only [MvForm.value, MvPolynomial.eval_add, hx]
    rw [hval]; exact hgen

@[simp] theorem add_P (p q : MvForm R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).P = p.P + q.P := rfl
@[simp] theorem add_x (p q : MvForm R n) (hx hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).x = p.x := rfl

@[simp] theorem add_value (p q : MvForm R n) (hx : p.x = q.x) (hsum_ne hfin) :
    (p.add q hx hsum_ne hfin).value = p.value + q.value := by
  simp only [MvForm.value, add_x, add_P, MvPolynomial.eval_add, hx]

/-- **Multiplication — EXACT, no leak.** Ideals multiply (`P · Q`); because polynomials are closed
under `×` and `eval` is a ring hom, the product is a genuine polynomial caught with *only* the FP
rounding error — no degree leak, no input bound. This is what `AffineForm.mul`/`QuadForm.mul` would
be if they did not have to truncate back to a fixed degree. -/
noncomputable def mul (p q : MvForm R n) (hx : p.x = q.x)
    (hprod_ne : (p.fp.toVal : R) * q.fp.toVal ≠ 0)
    (hfin : (p.fp * q.fp).isFinite) : MvForm R n where
  fp := (p.fp * q.fp).toFiniteOr0
  P := p.P * q.P
  x := p.x
  err := η * |p.value * q.value|
          + (1 + η) * (|p.value| * q.err + p.err * |q.value| + p.err * q.err)
          + (2 : R) ^ (FloatFormat.min_exp - FloatFormat.prec : ℤ)
  herr := by
    have hb := fpMulFinite_inexact_general p.fp q.fp p.value q.value p.err q.err _
      p.abs_toVal_sub_value_le q.abs_toVal_sub_value_le hprod_ne (Fp.eq_finite_toFiniteOr0 hfin)
    have hval : MvPolynomial.eval p.x (p.P * q.P) = p.value * q.value := by
      simp only [MvForm.value, MvPolynomial.eval_mul, hx]
    rw [hval]; exact hb

@[simp] theorem mul_P (p q : MvForm R n) (hx hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).P = p.P * q.P := rfl
@[simp] theorem mul_x (p q : MvForm R n) (hx hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).x = p.x := rfl

/-- The product form's ideal is `value p · value q` — exactly, no leak. -/
@[simp] theorem mul_value (p q : MvForm R n) (hx : p.x = q.x) (hprod_ne hfin) :
    (p.mul q hx hprod_ne hfin).value = p.value * q.value := by
  simp only [MvForm.value, mul_x, mul_P, MvPolynomial.eval_mul, hx]

end Compose

/-- **Negation** — total and exact; ideal `↦ −P`. -/
noncomputable def neg (p : MvForm R n) : MvForm R n where
  fp := -p.fp
  P := -p.P
  x := p.x
  err := p.err
  herr := by
    rw [FiniteFp.toVal_neg_eq_neg, map_neg,
      show -(p.fp.toVal : R) - -MvPolynomial.eval p.x p.P
        = -((p.fp.toVal : R) - MvPolynomial.eval p.x p.P) by ring, abs_neg]
    exact p.herr

@[simp] theorem neg_P (p : MvForm R n) : p.neg.P = -p.P := rfl
@[simp] theorem neg_x (p : MvForm R n) : p.neg.x = p.x := rfl
@[simp] theorem neg_err (p : MvForm R n) : p.neg.err = p.err := rfl

@[simp] theorem neg_value (p : MvForm R n) : p.neg.value = -p.value := by
  simp only [MvForm.value, neg_x, neg_P, map_neg]

end MvForm
