import Flean.Operations.ExactIntSign

/-! # The sign × magnitude **reduced product** — where addition closes

`ExactIntSign` exhibited the boundary: the exact-sign shadow factors `×` like a hom but does
**not** close under `+`. The diagnosis there was that sign closes under `+` only as a *reduced
product* with a magnitude domain — the off-diagonal sign of a sum is recoverable, but only with
magnitude separation. This file builds that reduced product and discharges the promise: a domain
carrying **both** a sign and a magnitude interval `[lo, hi]` on which `+` is **total** (no
same-sign precondition), because the magnitude data decides the off-diagonal case.

`HasSignMag s lo hi a` bundles `SignType.sign a.n = s` with `0 ≤ lo ≤ |a.n| ≤ hi`. It is the
**meet** of the two domains: it projects to the sign shadow (`toSign`) and to the magnitude
upper bound (`le_hi`, the `ExactIntB` content). The propagation:

* `mul` — sign multiplies (hom), magnitude interval multiplies. Unconditional.
* `add_same` — equal signs: sign preserved, interval `[lo_a+lo_b, hi_a+hi_b]` (magnitudes add
  exactly, `abs_add_of_sign_eq`). Unconditional.
* `add_dominant` — **the payoff**: signs *may differ*; if the lesser term is capped below the
  dominant's floor (`hi_b < lo_a`) the result takes the dominant's sign, interval
  `[lo_a−hi_b, hi_a+hi_b]`. This is the closure neither factor has alone.

Headline `add_stays_pos`: a dominant positive value plus *any* sufficiently-smaller value stays
positive — opposite-sign addition certified, which the sign domain could not do and the magnitude
domain has no notion of. This is the first genuine reduced product in the reduction stack.
-/

open SignType

/-! ## Pure `ℤ`/`sign` helper for same-sign magnitude addition -/

/-- Equal signs make magnitudes add exactly: `|x + y| = |x| + |y|`. (The reverse triangle
inequality becomes equality precisely when the two terms do not oppose.) -/
theorem abs_add_of_sign_eq {x y : ℤ} (h : SignType.sign x = SignType.sign y) :
    |x + y| = |x| + |y| := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : y < 0 := sign_eq_neg_one_iff.mp (by rw [← h]; exact sign_neg hx)
    rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg hx, abs_of_neg hy]; ring
  · have hy : y = 0 := sign_eq_zero_iff.mp (by rw [← h, hx, sign_zero])
    rw [hx, hy]; simp
  · have hy : 0 < y := sign_eq_one_iff.mp (by rw [← h]; exact sign_pos hx)
    rw [abs_of_pos (show 0 < x + y by linarith), abs_of_pos hx, abs_of_pos hy]

namespace ExactInt

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The reduced product of the sign shadow and a magnitude interval: the represented integer has
sign `s` and `0 ≤ lo ≤ |n| ≤ hi`. -/
def HasSignMag (s : SignType) (lo hi : ℤ) (a : ExactInt R) : Prop :=
  SignType.sign a.n = s ∧ 0 ≤ lo ∧ lo ≤ |a.n| ∧ |a.n| ≤ hi

/-! ## Projections — `HasSignMag` sits above both factor domains -/

theorem HasSignMag.sign_eq {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    SignType.sign a.n = s := h.1
theorem HasSignMag.lo_nonneg {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    0 ≤ lo := h.2.1
theorem HasSignMag.lo_le {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    lo ≤ |a.n| := h.2.2.1
theorem HasSignMag.le_hi {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    |a.n| ≤ hi := h.2.2.2
/-- Forget the magnitude: project onto the sign shadow. -/
theorem HasSignMag.toSign {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    HasSign s a := h.1

/-! ## Total ops -/

@[simp] theorem hasSignMag_zero : HasSignMag (R := R) 0 0 0 (0 : ExactInt R) := by
  refine ⟨?_, le_refl 0, ?_, ?_⟩ <;> simp [ExactInt.zero_n]

@[simp] theorem hasSignMag_one : HasSignMag (R := R) 1 1 1 (1 : ExactInt R) := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · show SignType.sign (1 : ExactInt R).n = 1
    rw [ExactInt.one_n, sign_one]
  · simp [ExactInt.one_n]
  · simp [ExactInt.one_n]

theorem HasSignMag.neg {s lo hi} {a : ExactInt R} (h : HasSignMag s lo hi a) :
    HasSignMag (-s) lo hi (-a) := by
  refine ⟨?_, h.lo_nonneg, ?_, ?_⟩
  · show SignType.sign (-a).n = -s
    rw [ExactInt.neg_n, Left.sign_neg, h.sign_eq]
  · rw [ExactInt.neg_n, abs_neg]; exact h.lo_le
  · rw [ExactInt.neg_n, abs_neg]; exact h.le_hi

/-! ## Partial ops -/

section Partial
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

/-- Multiplication: sign multiplies (hom), magnitude interval multiplies. Unconditional. -/
theorem HasSignMag.mul {s_a s_b : SignType} {lo_a hi_a lo_b hi_b : ℤ} {a b : ExactInt R}
    (ha : HasSignMag s_a lo_a hi_a a) (hb : HasSignMag s_b lo_b hi_b b)
    (hbound : (a.n * b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSignMag (s_a * s_b) (lo_a * lo_b) (hi_a * hi_b) (a.mul b hbound h_exp) := by
  refine ⟨?_, mul_nonneg ha.lo_nonneg hb.lo_nonneg, ?_, ?_⟩
  · show SignType.sign (a.mul b hbound h_exp).n = s_a * s_b
    rw [ExactInt.mul_n, sign_mul, ha.sign_eq, hb.sign_eq]
  · rw [ExactInt.mul_n, abs_mul]
    exact mul_le_mul ha.lo_le hb.lo_le hb.lo_nonneg (abs_nonneg _)
  · rw [ExactInt.mul_n, abs_mul]
    exact mul_le_mul ha.le_hi hb.le_hi (abs_nonneg _) (le_trans (abs_nonneg _) ha.le_hi)

/-- Same-sign addition: sign preserved, interval `[lo_a+lo_b, hi_a+hi_b]`. Unconditional given
the signs agree. -/
theorem HasSignMag.add_same {s : SignType} {lo_a hi_a lo_b hi_b : ℤ} {a b : ExactInt R}
    (ha : HasSignMag s lo_a hi_a a) (hb : HasSignMag s lo_b hi_b b)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSignMag s (lo_a + lo_b) (hi_a + hi_b) (a.add b hbound h_exp) := by
  have habs : |a.n + b.n| = |a.n| + |b.n| :=
    abs_add_of_sign_eq (by rw [ha.sign_eq, hb.sign_eq])
  refine ⟨?_, add_nonneg ha.lo_nonneg hb.lo_nonneg, ?_, ?_⟩
  · show SignType.sign (a.add b hbound h_exp).n = s
    rw [ExactInt.add_n]; exact sign_add_of_sign_eq ha.sign_eq hb.sign_eq
  · rw [ExactInt.add_n, habs]; exact add_le_add ha.lo_le hb.lo_le
  · rw [ExactInt.add_n, habs]; exact add_le_add ha.le_hi hb.le_hi

/-- **Dominant addition — the reduced product's payoff.** The signs may oppose; if the lesser
term's magnitude ceiling is below the dominant's floor (`hi_b < lo_a`), the sum takes the
dominant's sign, with interval `[lo_a−hi_b, hi_a+hi_b]`. Closure that neither factor domain has
on its own. -/
theorem HasSignMag.add_dominant {s_a s_b : SignType} {lo_a hi_a lo_b hi_b : ℤ} {a b : ExactInt R}
    (ha : HasSignMag s_a lo_a hi_a a) (hb : HasSignMag s_b lo_b hi_b b)
    (hsep : hi_b < lo_a)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSignMag s_a (lo_a - hi_b) (hi_a + hi_b) (a.add b hbound h_exp) := by
  have hdom : |b.n| < |a.n| := lt_of_le_of_lt hb.le_hi (lt_of_lt_of_le hsep ha.lo_le)
  have hrev : |a.n| - |b.n| ≤ |a.n + b.n| := by
    simpa using abs_sub_abs_le_abs_sub a.n (-b.n)
  refine ⟨?_, by linarith [hsep], ?_, ?_⟩
  · show SignType.sign (a.add b hbound h_exp).n = s_a
    rw [ExactInt.add_n, sign_add_of_abs_lt hdom]; exact ha.sign_eq
  · rw [ExactInt.add_n]; linarith [ha.lo_le, hb.le_hi, hrev]
  · rw [ExactInt.add_n]
    calc |a.n + b.n| ≤ |a.n| + |b.n| := abs_add_le _ _
      _ ≤ hi_a + hi_b := add_le_add ha.le_hi hb.le_hi

/-! ## Headline: opposite-sign addition that provably preserves the sign -/

/-- A dominant positive value plus *any* value (any sign `s_b`) whose magnitude ceiling sits
below the positive's floor stays positive. The sign survives an opposite-sign addition — exactly
the certification the sign domain alone could not produce. -/
theorem add_stays_pos {s_b : SignType} {lo_a hi_a lo_b hi_b : ℤ} {a b : ExactInt R}
    (ha : HasSignMag 1 lo_a hi_a a) (hb : HasSignMag s_b lo_b hi_b b)
    (hsep : hi_b < lo_a)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSign 1 (a.add b hbound h_exp) :=
  (ha.add_dominant hb hsep hbound h_exp).toSign

end Partial

end ExactInt
