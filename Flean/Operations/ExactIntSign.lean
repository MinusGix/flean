import Flean.Operations.ExactIntAlgebra
import Mathlib.Data.Sign.Basic

/-! # The exact-sign domain: the first *non-ring-hom* structural shadow

`ExactIntModP` built structural shadows that are **ring-hom images** of the exact integer `a.n`
(`IsImage` at a `CommRing S`): residue mod p, CRT, the exact value itself. Those all factor
uniformly because `ℤ → S` is a ring hom, so it commutes with *both* `+` and `×`.

This file builds the first shadow that is **not** a ring-hom image, to probe the boundary of that
framework. The shadow is the **exact sign** `SignType.sign a.n ∈ {−1, 0, +1}`. And `{−1,0,+1}` is
not a ring — it is not closed under `+` (`1 + 1` would be `2`). So sign cannot be an `IsImage`
instance. What it *is*: a **multiplicative monoid-with-zero hom** (`signHom : ℤ →*₀ SignType`,
`sign (x·y) = sign x · sign y`). The consequence, made precise below, is the framework lesson:

* **`mul` factors like a hom** — `HasSign.mul` is the exact analogue of `IsImage.mul`, a clean
  `sign·sign` law, no side conditions on the signs. (Likewise `zero`/`one`/`neg`.)
* **`add` does NOT factor** — there is no `sign (x+y)` as a function of `sign x`, `sign y` alone.
  The most we get unconditionally is the **diagonal** `HasSign.add_same` (equal signs are
  preserved); off the diagonal the sign of a sum is recoverable only with **magnitude**
  information (`HasSign.add_dominant`, needing `|b.n| < |a.n|`).

So the sign domain is genuinely a different family: the multiplicative part has its own would-be
light helper (a `ℤ →*₀ M`-image, parallel to `IsImage`'s `ℤ →+* S`-image), but the additive part
escapes it — sign is closed under `+` only as a **reduced product with the magnitude domain**.
That is exactly why the uniform `AbstractFp` typeclass was the wrong call: even *within* one
shadow, `+` and `×` want different machinery. (We build sign concretely here; whether to factor
out a generic `→*₀`-image helper waits for a second multiplicative instance, mirroring how
`IsImage` waited for mod-p's second case.)

Headline (`dot2_pos`): an all-positive integer dot product is provably positive — sign extracted
from sign alone, the flavour of ReLU / loss-positivity arguments. `HasSign.pos` bridges back to a
genuine fact about the float value.
-/

open SignType

/-! ## Pure `ℤ`/`sign` helpers (no float content) -/

/-- Equal signs are preserved by addition — the diagonal of the (otherwise non-existent) additive
sign law. Mirrors `sign_sum` for two terms. -/
theorem sign_add_of_sign_eq {x y : ℤ} {s : SignType}
    (hx : SignType.sign x = s) (hy : SignType.sign y = s) : SignType.sign (x + y) = s := by
  cases s
  · simp_rw [SignType.zero_eq_zero, sign_eq_zero_iff] at hx hy ⊢
    rw [hx, hy, add_zero]
  · simp_rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] at hx hy ⊢
    linarith
  · simp_rw [SignType.pos_eq_one, sign_eq_one_iff] at hx hy ⊢
    linarith

/-- Off the diagonal, the sign of a sum needs **magnitude**: the dominant term sets the sign.
This is the seam where the sign domain must reduce-product with a magnitude domain to close `+`. -/
theorem sign_add_of_abs_lt {x y : ℤ} (h : |y| < |x|) :
    SignType.sign (x + y) = SignType.sign x := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx] at h1 h2
    rw [sign_neg hx, sign_neg (by linarith)]
  · exfalso; rw [hx, abs_zero] at h; exact absurd h (not_lt.mpr (abs_nonneg y))
  · rw [abs_of_pos hx] at h1 h2
    rw [sign_pos hx, sign_pos (by linarith)]

namespace ExactInt

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The exact-sign shadow: the sign of the represented integer is `s : SignType`. -/
def HasSign (s : SignType) (a : ExactInt R) : Prop := SignType.sign a.n = s

/-! ## Total ops: `zero`/`one`/`neg` — the part that factors unconditionally -/

@[simp] theorem hasSign_zero : HasSign (R := R) 0 (0 : ExactInt R) := by simp [HasSign]
@[simp] theorem hasSign_one : HasSign (R := R) 1 (1 : ExactInt R) := by simp [HasSign]

theorem HasSign.neg {s : SignType} {a : ExactInt R} (ha : HasSign s a) : HasSign (-s) (-a) := by
  show SignType.sign (-a).n = -s
  rw [neg_n, Left.sign_neg, ha]

/-- The value-positivity bridge: a `HasSign 1` shadow is a genuine fact about the float — its real
value is strictly positive. (`-1`/`0` analogues are immediate from `sign_eq_neg_one_iff`/`…`.) -/
theorem HasSign.pos {a : ExactInt R} (ha : HasSign 1 a) : 0 < (a.fp.toVal : R) := by
  rw [a.agree]; exact_mod_cast sign_eq_one_iff.mp ha

/-! ## Multiplication: factors like a hom (`sign_mul`), no side conditions on the signs -/

section Partial
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

theorem HasSign.mul {s_a s_b : SignType} {a b : ExactInt R}
    (ha : HasSign s_a a) (hb : HasSign s_b b)
    (hbound : (a.n * b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSign (s_a * s_b) (a.mul b hbound h_exp) := by
  show SignType.sign (a.mul b hbound h_exp).n = s_a * s_b
  rw [mul_n, sign_mul, ha, hb]

/-! ## Addition: does NOT factor — only the diagonal, or with magnitude -/

/-- **Diagonal addition.** Equal signs survive a sum. This is the *most* `+` gives from sign data
alone — note it is conditional on the two signs *agreeing*, so it is not a function of the input
signs the way `HasSign.mul` is. -/
theorem HasSign.add_same {s : SignType} {a b : ExactInt R}
    (ha : HasSign s a) (hb : HasSign s b)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSign s (a.add b hbound h_exp) := by
  show SignType.sign (a.add b hbound h_exp).n = s
  rw [add_n]; exact sign_add_of_sign_eq ha hb

/-- **Dominant addition.** Off the diagonal the sum's sign is set by the larger-magnitude term —
but this needs a *magnitude* hypothesis `|b.n| < |a.n|`, which the sign domain alone does not
carry. The seam where sign must reduce-product with a magnitude/interval domain (`ExactIntB`). -/
theorem HasSign.add_dominant {s_a : SignType} {a b : ExactInt R}
    (ha : HasSign s_a a) (hdom : |b.n| < |a.n|)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSign s_a (a.add b hbound h_exp) := by
  show SignType.sign (a.add b hbound h_exp).n = s_a
  rw [add_n, sign_add_of_abs_lt hdom, ha]

/-! ## Headline: an all-positive dot product is provably positive

`mul` gives each product sign `1·1 = 1`; the diagonal `add_same` then carries `1` through the sum.
The sign of the whole float computation is extracted from the inputs' signs alone. -/

theorem dot2_pos {a₁ b₁ a₂ b₂ : ExactInt R}
    (ha₁ : HasSign 1 a₁) (hb₁ : HasSign 1 b₁)
    (ha₂ : HasSign 1 a₂) (hb₂ : HasSign 1 b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    HasSign 1 (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) := by
  have hp1 : HasSign (1 * 1) (a₁.mul b₁ h₁b h_exp) := ha₁.mul hb₁ h₁b h_exp
  have hp2 : HasSign (1 * 1) (a₂.mul b₂ h₂b h_exp) := ha₂.mul hb₂ h₂b h_exp
  simp only [one_mul] at hp1 hp2
  exact hp1.add_same hp2 hsb h_exp

end Partial

end ExactInt
