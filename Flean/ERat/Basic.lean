/-

# The Extended Rational Numbers
99% from the mathlib definition of `EReal`.



-/
import Batteries.Data.Rat
import Mathlib.Order.TypeTags
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Flean.ENNRat.Basic

section

open Function Set ENNRat

def ERat := WithBot (WithTop ℚ)
  deriving Bot, Zero, One, Nontrivial, AddMonoid, PartialOrder, AddCommMonoid

instance : ZeroLEOneClass ERat := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℚ)))

instance : LinearOrder ERat := inferInstanceAs (LinearOrder (WithBot (WithTop ℚ)))

instance : Lattice ERat := inferInstanceAs (Lattice (WithBot (WithTop ℚ)))

instance : IsOrderedAddMonoid ERat := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop ℚ)))

instance : AddCommMonoidWithOne ERat := inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop ℚ)))

instance : CharZero ERat := inferInstanceAs (CharZero (WithBot (WithTop ℚ)))

@[coe] def Rat.toERat : ℚ → ERat := WithBot.some ∘ WithTop.some

namespace ERat

instance decidableLT : DecidableLT ERat := WithBot.decidableLT

instance : Top ERat := ⟨WithBot.some ⊤⟩

-- TODO: EReal gets this from somewhere else, probably we're missing some nice instances?
instance : OrderTop ERat := inferInstanceAs (OrderTop (WithBot (WithTop ℚ)))

instance : OrderBot ERat := inferInstanceAs (OrderBot (WithBot (WithTop ℚ)))

instance : BoundedOrder ERat := inferInstanceAs (BoundedOrder (WithBot (WithTop ℚ)))

instance : Lattice ERat := inferInstanceAs (Lattice (WithBot (WithTop ℚ)))

instance : Coe ℚ ERat := ⟨Rat.toERat⟩

theorem coe_strictMono : StrictMono Rat.toERat := WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Injective Rat.toERat := coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℚ} : (x : ERat) ≤ (y : ERat) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := ERat.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℚ} : (x : ERat) < (y : ERat) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := ERat.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℚ} : (x : ERat) = (y : ERat) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℚ} : (x : ERat) ≠ (y : ERat) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
protected theorem coe_natCast {n : ℕ} : ((n : ℚ) : ERat) = n := rfl

/-- The canonical map from nonnegative extended reals to extended Rationals. -/
@[coe] def _root_.ENNRat.toERat : ℚ≥0∞ → ERat
  | ⊤ => ⊤
  | .some x => x.1

instance hasCoeENNRat : Coe ℚ≥0∞ ERat :=
  ⟨ENNRat.toERat⟩

instance : Inhabited ERat := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ) : ERat) = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ) : ERat) = 1 := rfl

/-- A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {motive : ERat → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℚ, motive a) (top : motive ⊤) : ∀ a : ERat, motive a
  | ⊥ => bot
  | (a : ℚ) => coe a
  | ⊤ => top

protected lemma «forall» {p : ERat → Prop} : (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : ℚ, p r where
  mp h := ⟨h _, h _, fun _ ↦ h _⟩
  mpr h := ERat.rec h.1 h.2.2 h.2.1

protected lemma «exists» {p : ERat → Prop} : (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : ℚ, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/-- The multiplication on `EReal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected def mul : ERat → ERat → ERat
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : ℚ) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℚ) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : ℚ), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : ℚ), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : ℚ), (y : ℚ) => (x * y : ℚ)

instance : Mul ERat := ⟨ERat.mul⟩

@[simp, norm_cast]
theorem coe_mul (x y : ℚ) : (↑(x * y) : ERat) = x * y :=
  rfl

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : ERat → ERat → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : ℚ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℚ, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : ℚ, x < 0 → P x ⊤)
    (neg_bot : ∀ x : ℚ, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : ℚ, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : ℚ, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : ℚ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : ℚ), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : ℚ), (y : ℚ) => coe_coe _ _
  | (x : ℚ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℚ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : ERat → ERat → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℚ, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℚ, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

protected theorem mul_comm (x y : ERat) : x * y = y * x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

protected theorem one_mul : ∀ x : ERat, 1 * x = x
  | ⊤ => by simp [instHMul, instMul, ERat.mul]
  | ⊥ => by simp [instHMul, instMul, ERat.mul]
  | (x : ℚ) => congr_arg Rat.toERat (one_mul x)

protected theorem zero_mul : ∀ x : ERat, 0 * x = 0
  | ⊤ => by simp [instHMul, instMul, ERat.mul]
  | ⊥ => by simp [instHMul, instMul, ERat.mul]
  | (x : ℚ) => congr_arg Rat.toERat (zero_mul x)

instance : MulZeroOneClass ERat where
  one_mul := ERat.one_mul
  mul_one := fun x => by rw [ERat.mul_comm, ERat.one_mul]
  zero_mul := ERat.zero_mul
  mul_zero := fun x => by rw [ERat.mul_comm, ERat.zero_mul]

/-! ### Real coercion -/

instance canLift : CanLift ERat ℚ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended reals to reals sending infinities to zero. -/
def toRat : ERat → ℚ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℚ) => x

@[simp]
theorem toRat_top : toRat ⊤ = 0 :=
  rfl

@[simp]
theorem toRat_bot : toRat ⊥ = 0 :=
  rfl

@[simp]
theorem toRat_zero : toRat 0 = 0 :=
  rfl

@[simp]
theorem toRat_one : toRat 1 = 1 :=
  rfl

@[simp]
theorem toRat_coe (x : ℚ) : toRat (x : ERat) = x :=
  rfl

@[simp]
theorem bot_lt_coe (x : ℚ) : (⊥ : ERat) < x :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : ℚ) : (x : ERat) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
theorem bot_ne_coe (x : ℚ) : (⊥ : ERat) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
theorem coe_lt_top (x : ℚ) : (x : ERat) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : ℚ) : (x : ERat) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
theorem top_ne_coe (x : ℚ) : (⊤ : ERat) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem bot_lt_zero : (⊥ : ERat) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero : (⊥ : ERat) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot : (0 : ERat) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top : (0 : ERat) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : ERat) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : ERat) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : range Rat.toERat = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp

theorem range_coe_eq_Ioo : range Rat.toERat = Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
theorem coe_add (x y : ℚ) : (↑(x + y) : ERat) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_nsmul (⟨⟨Rat.toERat, coe_zero⟩, coe_add⟩ : ℚ →+ ERat) _ _

@[simp, norm_cast]
theorem coe_eq_zero {x : ℚ} : (x : ERat) = 0 ↔ x = 0 :=
  ERat.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : ℚ} : (x : ERat) = 1 ↔ x = 1 :=
  ERat.coe_eq_coe_iff

theorem coe_ne_zero {x : ℚ} : (x : ERat) ≠ 0 ↔ x ≠ 0 :=
  ERat.coe_ne_coe_iff

theorem coe_ne_one {x : ℚ} : (x : ERat) ≠ 1 ↔ x ≠ 1 :=
  ERat.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℚ} : (0 : ERat) ≤ x ↔ 0 ≤ x :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℚ} : (x : ERat) ≤ 0 ↔ x ≤ 0 :=
  ERat.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : ℚ} : (0 : ERat) < x ↔ 0 < x :=
  ERat.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' {x : ℚ} : (x : ERat) < 0 ↔ x < 0 :=
  ERat.coe_lt_coe_iff

lemma toRat_eq_zero_iff {x : ERat} : x.toRat = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> norm_num

lemma toRat_ne_zero_iff {x : ERat} : x.toRat ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  simp only [ne_eq, toRat_eq_zero_iff, not_or]

lemma toRat_eq_toRat {x y : ERat} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toRat = y.toRat ↔ x = y := by
  lift x to ℚ using ⟨hx_top, hx_bot⟩
  lift y to ℚ using ⟨hy_top, hy_bot⟩
  simp

lemma toRat_nonneg {x : ERat} (hx : 0 ≤ x) : 0 ≤ x.toRat := by
  cases x
  · norm_num
  · exact toRat_coe _ ▸ ERat.coe_nonneg.mp hx
  · norm_num

lemma toRat_nonpos {x : ERat} (hx : x ≤ 0) : x.toRat ≤ 0 := by
  cases x
  · norm_num
  · exact toRat_coe _ ▸ ERat.coe_nonpos.mp hx
  · norm_num

theorem toRat_le_toRat {x y : ERat} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toRat ≤ y.toRat := by
  lift x to ℚ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to ℚ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

theorem coe_toRat {x : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toRat : ERat) = x := by
  lift x to ℚ using ⟨hx, h'x⟩
  rfl

theorem le_coe_toRat {x : ERat} (h : x ≠ ⊤) : x ≤ x.toRat := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toRat h h']

theorem coe_toRat_le {x : ERat} (h : x ≠ ⊥) : ↑x.toRat ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toRat h' h]

theorem eq_top_iff_forall_lt (x : ERat) : x = ⊤ ↔ ∀ y : ℚ, (y : ERat) < x := by
  constructor
  · rintro rfl
    exact ERat.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toRat, le_coe_toRat h⟩

theorem eq_bot_iff_forall_lt (x : ERat) : x = ⊥ ↔ ∀ y : ℚ, x < (y : ERat) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toRat, coe_toRat_le h⟩


end ERat

end
