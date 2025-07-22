/-
# Extended Numbers

The core idea for this is to unify Extended Rs and ERats primarily, as they behave quite similarly and share many properties.

As well, a hope is to make being generic over the two types easier, as it is an "automatic" extension of the type,
such you can merely write `Extended <type>` to get the extended version of the type.

-/

import Batteries.Data.Rat
import Mathlib.Order.TypeTags
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Batteries.Data.Rat
import Mathlib.Order.TypeTags
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Order.Interval.Set.WithBotTop
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Tactic.Finiteness
import Mathlib.Data.NNRat.Order
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Algebra.Field.Rat
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Archimedean.Basic


def Extended (R : Type*) := WithBot (WithTop R)

open Function Set

namespace Extended

variable {R : Type*}

-- Coercions --
-- @[coe] def fromBase : R → Extended R := WithBot.some ∘ WithTop.some
@[coe] def fromBase (r : R) : Extended R := WithBot.some (WithTop.some r)

-- instance : Coe R (Extended R) := ⟨fromBase⟩
instance : Coe R (Extended R) := ⟨fromBase⟩

-- BASIC --
instance : Bot (Extended R) := inferInstanceAs (Bot (WithBot (WithTop R)))

instance : Top (Extended R) := ⟨WithBot.some ⊤⟩

protected def beq [BEq R] (x y : Extended R) : Bool := match x, y with
  | ⊥, ⊥ => true
  | ⊥, _ => false
  | ⊤, ⊤ => true
  | ⊤, _ => false
  | _, ⊥ => false
  | _, ⊤ => false
  | (x : R), (y : R) => x == y

instance [BEq R] : BEq (Extended R) := {
  beq := Extended.beq
}

instance [BEq R] [ReflBEq R] : ReflBEq (Extended R) := {
  rfl := by
    intro a
    unfold_projs
    unfold Extended.beq
    grind
}

instance [Zero R] : Zero (Extended R) := inferInstanceAs (Zero (WithBot (WithTop R)))

instance [One R] : One (Extended R) := inferInstanceAs (One (WithBot (WithTop R)))

instance [Nontrivial R] : Nontrivial (Extended R) := inferInstanceAs (Nontrivial (WithBot (WithTop R)))

instance [NatCast R] : NatCast (Extended R) := {
  natCast := fun n => ↑(n : R)
}

-- instance (n : ℕ) [OfNat R n] : OfNat (Extended R) n := ⟨fromBase (OfNat.ofNat n)⟩

-- Operations --
instance [Add R] : Add (Extended R) := inferInstanceAs (Add (WithBot (WithTop R)))

instance [AddMonoid R] : AddMonoid (Extended R) := inferInstanceAs (AddMonoid (WithBot (WithTop R)))

instance [AddCommMonoid R] : AddCommMonoid (Extended R) := inferInstanceAs (AddCommMonoid (WithBot (WithTop R)))

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Extended R) := inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop R)))

instance [AddCommMonoidWithOne R] [CharZero R] : CharZero (Extended R) := inferInstanceAs (CharZero (WithBot (WithTop R)))

noncomputable instance [Preorder R] [SupSet R] : SupSet (Extended R) := inferInstanceAs (SupSet (WithBot (WithTop R)))

noncomputable instance [Preorder R] [InfSet R] : InfSet (Extended R) := inferInstanceAs (InfSet (WithBot (WithTop R)))

-- Order --
instance [Lattice R] : Lattice (Extended R) := inferInstanceAs (Lattice (WithBot (WithTop R)))

instance [LT R] : LT (Extended R) := inferInstanceAs (LT (WithBot (WithTop R)))

instance [LE R] : LE (Extended R) := inferInstanceAs (LE (WithBot (WithTop R)))

instance [Preorder R] : Preorder (Extended R) := inferInstanceAs (Preorder (WithBot (WithTop R)))

instance [PartialOrder R] : PartialOrder (Extended R) := inferInstanceAs (PartialOrder (WithBot (WithTop R)))

instance [LinearOrder R] : LinearOrder (Extended R) := inferInstanceAs (LinearOrder (WithBot (WithTop R)))

instance [LT R] [DecidableLT R] : DecidableLT (Extended R) := WithBot.decidableLT

instance [LE R] : OrderTop (Extended R) := inferInstanceAs (OrderTop (WithBot (WithTop R)))

instance [LE R] : OrderBot (Extended R) := inferInstanceAs (OrderBot (WithBot (WithTop R)))

noncomputable instance [ConditionallyCompleteLinearOrder R] : CompleteLinearOrder (Extended R) := inferInstanceAs (CompleteLinearOrder (WithBot (WithTop R)))

noncomputable instance [Nonempty R] [LT R] [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R] : DenselyOrdered (Extended R) :=
  @WithBot.denselyOrdered (WithTop R) _ WithTop.instDenselyOrderedOfNoMaxOrder WithTop.noMinOrder

-- Order/Op --

instance [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R] : IsOrderedAddMonoid (Extended R) := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop R)))

-- Theorems --
theorem coe_strictMono [Preorder R] : StrictMono (fromBase (R := R)) := WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Injective (fromBase (R := R)) := λ _ _ h => Option.some_inj.mp (Option.some_inj.mp h)

@[simp, norm_cast]
protected theorem coe_le_coe_iff [LE R] {x y : R} : (x : Extended R) ≤ (y : Extended R) ↔ x ≤ y := WithBot.coe_le_coe.trans WithTop.coe_le_coe

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := Extended.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_lt_coe_iff [LT R] {x y : R} : (x : Extended R) < (y : Extended R) ↔ x < y :=
  WithBot.coe_lt_coe.trans WithTop.coe_lt_coe

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := Extended.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : R} : (x : Extended R) = (y : Extended R) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : R} : (x : Extended R) ≠ (y : Extended R) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
protected theorem coe_natCast [NatCast R] {n : ℕ} : ((n : R) : Extended R) = n := rfl

instance [Zero R] : Inhabited (Extended R) := ⟨0⟩

@[simp, norm_cast]
protected theorem coe_zero [Zero R] : ((0 : R) : Extended R) = 0 := rfl

@[simp, norm_cast]
protected theorem coe_one [One R] : ((1 : R) : Extended R) = 1 := rfl

/-- A recursor for `Extended R` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {motive : Extended R → Sort*}
    (bot : motive ⊥) (coe : ∀ a : R, motive a) (top : motive ⊤) : ∀ a : Extended R, motive a
  | ⊥ => bot
  | (a : R) => coe a
  | ⊤ => top

protected lemma «forall» {p : Extended R → Prop} : (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : R, p r where
  mp h := ⟨h _, h _, fun _ ↦ h _⟩
  mpr h := Extended.rec h.1 h.2.2 h.2.1

protected lemma «exists» {p : Extended R → Prop} : (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : R, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/-- The multiplication on `Extended R`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected def mul [Zero R] [LT R] [Mul R] [DecidableEq R] [DecidableLT R] : Extended R → Extended R → Extended R
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : R) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : R) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : R), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : R), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : R), (y : R) => (x * y : R)

instance [Zero R] [LT R] [Mul R] [DecidableEq R] [DecidableLT R] : Mul (Extended R) := ⟨Extended.mul⟩

@[simp, norm_cast]
theorem coe_mul [Zero R] [LT R] [Mul R] [DecidableEq R] [DecidableLT R] (x y : R) : (↑(x * y) : Extended R) = x * y :=
  rfl

/-- Induct on two `Extended R`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ [Zero R] [LinearOrder R] {P : Extended R → Extended R → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : R, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : R, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : R, 0 < x → P x ⊤) (pos_bot : ∀ x : R, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : R, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : R, x < 0 → P x ⊤)
    (neg_bot : ∀ x : R, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : R, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : R, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : R) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : R), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : R), (y : R) => coe_coe _ _
  | (x : R), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : R) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `Extended R`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm [Zero R] [LinearOrder R] {P : Extended R → Extended R → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : R, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : R, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : R, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : R, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : R, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ R _ _ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

protected theorem mul_comm [Zero R] [LT R] [CommMagma R] [DecidableEq R] [DecidableLT R] (x y : Extended R) : x * y = y * x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

protected theorem one_mul [Zero R] [MulOneClass R] [PartialOrder R] [ZeroLEOneClass R] [NeZero (1 : R)] [DecidableEq R] [DecidableLT R] : ∀ x : Extended R, 1 * x = x
  | ⊤ => if_pos one_pos
  | ⊥ => if_pos one_pos
  | (x : R) => congr_arg fromBase (one_mul x)

protected theorem zero_mul [MulZeroClass R] [Preorder R] [DecidableEq R] [DecidableLT R] : ∀ x : Extended R, 0 * x = 0
  | ⊤ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | ⊥ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | (x : R) => congr_arg fromBase (zero_mul x)

instance [PartialOrder R] [CommMonoidWithZero R] [ZeroLEOneClass R] [NeZero (1 : R)] [DecidableEq R] [DecidableLT R] : MulZeroOneClass (Extended R) where
  one_mul := Extended.one_mul
  mul_one := fun x => by rw [Extended.mul_comm (R := R), Extended.one_mul]
  zero_mul := Extended.zero_mul
  mul_zero := fun x => by rw [Extended.mul_comm, Extended.zero_mul]

/-! ### Base coercion -/

instance canLift : CanLift (Extended R) R (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended `R` to `R`, sending infinities to zero. -/
def toBase [Zero R] : Extended R → R
  | ⊥ => 0
  | ⊤ => 0
  | (x : R) => x

@[simp]
theorem toBase_top [Zero R] : toBase (R := R) ⊤ = 0 :=
  rfl

@[simp]
theorem toBase_bot [Zero R] : toBase (R := R) ⊥ = 0 :=
  rfl

@[simp]
theorem toBase_zero [Zero R] : toBase (R := R) 0 = 0 :=
  rfl

@[simp]
theorem toBase_one [Zero R] [One R] : toBase (R := R) 1 = 1 :=
  rfl

@[simp]
theorem toBase_coe [Zero R] (x : R) : toBase (x : Extended R) = x :=
  rfl

@[simp]
theorem bot_lt_coe [Zero R] [LT R] (x : R) : (⊥ : Extended R) < x :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : R) : (x : Extended R) ≠ ⊥ :=
  WithBot.coe_ne_bot

@[simp]
theorem bot_ne_coe (x : R) : (⊥ : Extended R) ≠ x :=
  WithBot.bot_ne_coe

@[simp]
theorem coe_lt_top [LT R] (x : R) : (x : Extended R) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : R) : (x : Extended R) ≠ ⊤ :=
  mt WithBot.coe_inj.mp (WithTop.coe_ne_top (a := x))

@[simp]
theorem top_ne_coe (x : R) : (⊤ : Extended R) ≠ x :=
  mt WithBot.coe_inj.mp (WithTop.coe_ne_top (a := x)).symm

@[simp]
theorem bot_lt_zero [Zero R] [LT R] : (⊥ : Extended R) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero [Zero R] : (⊥ : Extended R) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot [Zero R] : (0 : Extended R) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top [Zero R] [LT R] : (0 : Extended R) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top [Zero R] : (0 : Extended R) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero [Zero R] : (⊤ : Extended R) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : range (fromBase (R := R)) = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp

theorem range_coe_eq_Ioo [Zero R] [Preorder R] : range (fromBase (R := R)) = Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
theorem coe_add [Add R] (x y : R) : (↑(x + y) : Extended R) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul [NatCast R] [AddMonoid R] (n : ℕ) (x : R) : (↑(n • x) : Extended R) = n • (x : Extended R) :=
  map_nsmul (⟨⟨fromBase (R := R), Extended.coe_zero⟩, coe_add⟩ : R →+ Extended R) _ _

@[simp, norm_cast]
theorem coe_eq_zero [Zero R] {x : R} : (x : Extended R) = 0 ↔ x = 0 :=
  Extended.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one [One R] {x : R} : (x : Extended R) = 1 ↔ x = 1 :=
  Extended.coe_eq_coe_iff

theorem coe_ne_zero [Zero R] {x : R} : (x : Extended R) ≠ 0 ↔ x ≠ 0 :=
  Extended.coe_ne_coe_iff

theorem coe_ne_one [One R] {x : R} : (x : Extended R) ≠ 1 ↔ x ≠ 1 :=
  Extended.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg [Zero R] [LE R] {x : R} : (0 : Extended R) ≤ x ↔ 0 ≤ x :=
  Extended.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos [Zero R] [LE R] {x : R} : (x : Extended R) ≤ 0 ↔ x ≤ 0 :=
  Extended.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos [Zero R] [LT R] {x : R} : (0 : Extended R) < x ↔ 0 < x :=
  Extended.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' [Zero R] [LT R] {x : R} : (x : Extended R) < 0 ↔ x < 0 :=
  Extended.coe_lt_coe_iff

lemma toBase_eq_zero_iff [Zero R] {x : Extended R} : x.toBase = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> simp [toBase_bot]

lemma toBase_ne_zero_iff [Zero R] {x : Extended R} : x.toBase ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  simp only [ne_eq, toBase_eq_zero_iff, not_or]

lemma toBase_eq_toBase [Zero R] {x y : Extended R} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toBase = y.toBase ↔ x = y := by
  lift x to R using ⟨hx_top, hx_bot⟩
  lift y to R using ⟨hy_top, hy_bot⟩
  simp

lemma toBase_nonneg [Zero R] [Preorder R] {x : Extended R} (hx : 0 ≤ x) : 0 ≤ x.toBase := by
  cases x
  · norm_num
  · exact toBase_coe (R := R) _ ▸ Extended.coe_nonneg.mp hx
  · norm_num

lemma toBase_nonpos [Zero R] [Preorder R] {x : Extended R} (hx : x ≤ 0) : x.toBase ≤ 0 := by
  cases x
  · norm_num
  · exact toBase_coe (R := R) _ ▸ Extended.coe_nonpos.mp hx
  · norm_num

theorem toBase_le_toBase [Zero R] [PartialOrder R] {x y : Extended R} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toBase ≤ y.toBase := by
  lift x to R using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to R using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

theorem coe_toBase [Zero R] {x : Extended R} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toBase : Extended R) = x := by
  lift x to R using ⟨hx, h'x⟩
  rfl

theorem le_coe_toBase [Zero R] [Preorder R] {x : Extended R} (h : x ≠ ⊤) : x ≤ x.toBase := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toBase h h']

theorem coe_toBase_le [Zero R] [Preorder R] {x : Extended R} (h : x ≠ ⊥) : ↑x.toBase ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toBase h' h]

theorem eq_top_iff_forall_lt [Zero R] [Preorder R] (x : Extended R) : x = ⊤ ↔ ∀ y : R, (y : Extended R) < x := by
  constructor
  · rintro rfl
    exact Extended.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toBase, (le_coe_toBase h).not_gt⟩

theorem eq_bot_iff_forall_lt [Zero R] [Preorder R] (x : Extended R) : x = ⊥ ↔ ∀ y : R, x < (y : Extended R) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toBase, (coe_toBase_le h).not_gt⟩

/-! ### Intervals and coercion from base -/

-- TODO: can we just require DenselyOrdered (Extended R) to avoid these extra instances?
lemma exists_between_coe_real [Preorder R] [Nonempty R] [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R] {x z : Extended R} (h : x < z) : ∃ y : R, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot (α := Extended R) ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

@[simp]
lemma image_coe_Icc [Preorder R] (x y : R) : fromBase '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

@[simp]
lemma image_coe_Ico [Preorder R] (x y : R) : fromBase '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ici [Preorder R] (x : R) : fromBase '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ioc [Preorder R] (x y : R) : fromBase '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

@[simp]
lemma image_coe_Ioo [Preorder R] (x y : R) : fromBase '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Ioi [Preorder R] (x : R) : fromBase '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Iic [Preorder R] (x : R) : fromBase '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

@[simp]
lemma image_coe_Iio [Preorder R] (x : R) : fromBase '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

@[simp]
lemma preimage_coe_Ici [Preorder R] (x : R) : fromBase ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
lemma preimage_coe_Ioi [Preorder R] (x : R) : fromBase ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
lemma preimage_coe_Ioi_bot [Preorder R] : fromBase (R := R) ⁻¹' Ioi ⊥ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi ⊥) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
lemma preimage_coe_Iic [Preorder R] (y : R) : fromBase ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
  lemma preimage_coe_Iio [Preorder R] (y : R) : fromBase ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
lemma preimage_coe_Iio_top [Preorder R] : fromBase (R := R) ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some ⊤)) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
lemma preimage_coe_Icc [Preorder R] (x y : R) : fromBase ⁻¹' Icc x y = Icc x y := by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ico [Preorder R] (x y : R) : fromBase ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc [Preorder R] (x y : R) : fromBase ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo [Preorder R] (x y : R) : fromBase ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ico_top [Preorder R] (x : R) : fromBase ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_top [Preorder R] (x : R) : fromBase ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc_bot [Preorder R] (y : R) : fromBase ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo_bot [Preorder R] (y : R) : fromBase ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_bot_top [Preorder R] : fromBase (R := R) ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### ennreal coercion -/

-- @[simp]
-- theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
--   | ⊤ => rfl
--   | .some _ => rfl

-- @[simp]
-- theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
--   rfl

-- lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
--   lift x to ℝ≥0 using hx
--   rfl

-- theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : EReal) = 0 :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_ennreal_one : ((1 : ℝ≥0∞) : EReal) = 1 :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : EReal) = ⊤ :=
--   rfl

-- theorem coe_ennreal_strictMono : StrictMono ((↑) : ℝ≥0∞ → EReal) :=
--   WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩

-- theorem coe_ennreal_injective : Injective ((↑) : ℝ≥0∞ → EReal) :=
--   coe_ennreal_strictMono.injective

-- @[simp]
-- theorem coe_ennreal_eq_top_iff {x : ℝ≥0∞} : (x : EReal) = ⊤ ↔ x = ⊤ :=
--   coe_ennreal_injective.eq_iff' rfl

-- theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := coe_ne_top x

-- @[simp]
-- theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := coe_lt_top x

-- @[simp, norm_cast]
-- theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
--   coe_ennreal_strictMono.le_iff_le

-- @[simp, norm_cast]
-- theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
--   coe_ennreal_strictMono.lt_iff_lt

-- @[simp, norm_cast]
-- theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
--   coe_ennreal_injective.eq_iff

-- theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
--   coe_ennreal_injective.ne_iff

-- @[simp, norm_cast]
-- theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : EReal) = 0 ↔ x = 0 := by
--   rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]

-- @[simp, norm_cast]
-- theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
--   rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]

-- @[norm_cast]
-- theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
--   coe_ennreal_eq_zero.not

-- @[norm_cast]
-- theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
--   coe_ennreal_eq_one.not

-- theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
--   coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)

-- @[simp] theorem range_coe_ennreal : range ((↑) : ℝ≥0∞ → EReal) = Set.Ici 0 :=
--   Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
--     | ⊥ => fun h => absurd h bot_lt_zero.not_ge
--     | ⊤ => fun _ => ⟨⊤, rfl⟩
--     | (x : ℝ) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

-- instance : CanLift EReal ℝ≥0∞ (↑) (0 ≤ ·) := ⟨range_coe_ennreal.ge⟩

-- @[simp, norm_cast]
-- theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
--   rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]

-- theorem coe_ennreal_pos_iff_ne_zero {x : ℝ≥0∞} : (0 : EReal) < x ↔ x ≠ 0 := by
--   rw [coe_ennreal_pos, pos_iff_ne_zero]

-- @[simp]
-- theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : EReal) < x :=
--   (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

-- @[simp]
-- theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : EReal) ≠ ⊥ :=
--   (bot_lt_coe_ennreal x).ne'

-- @[simp, norm_cast]
-- theorem coe_ennreal_add (x y : ENNReal) : ((x + y : ℝ≥0∞) : EReal) = x + y := by
--   cases x <;> cases y <;> rfl

-- private theorem coe_ennreal_top_mul (x : ℝ≥0) : ((⊤ * x : ℝ≥0∞) : EReal) = ⊤ * x := by
--   rcases eq_or_ne x 0 with (rfl | h0)
--   · simp
--   · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
--     exact Eq.symm <| if_pos <| NNReal.coe_pos.2 h0.bot_lt

-- @[simp, norm_cast]
-- theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = (x : EReal) * y
--   | ⊤, ⊤ => rfl
--   | ⊤, (y : ℝ≥0) => coe_ennreal_top_mul y
--   | (x : ℝ≥0), ⊤ => by
--     rw [mul_comm, coe_ennreal_top_mul, EReal.mul_comm, coe_ennreal_top]
--   | (x : ℝ≥0), (y : ℝ≥0) => by
--     simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]

-- @[norm_cast]
-- theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • (x : EReal) :=
--   map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _

/-! ### toENNReal -/

-- /-- `x.toENNReal` returns `x` if it is nonnegative, `0` otherwise. -/
-- noncomputable def toENNReal (x : EReal) : ℝ≥0∞ :=
--   if x = ⊤ then ⊤
--   else ENNReal.ofReal x.toReal

-- @[simp] lemma toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

-- @[simp]
-- lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
--   if_neg hx

-- @[simp]
-- lemma toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
--   by_cases h : x = ⊤
--   · simp [h]
--   · simp [h, toENNReal]

-- lemma toENNReal_ne_top_iff {x : EReal} : x.toENNReal ≠ ⊤ ↔ x ≠ ⊤ := toENNReal_eq_top_iff.not

-- @[simp]
-- lemma toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0 := by
--   rw [toENNReal, if_neg (fun h ↦ ?_)]
--   · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
--   · exact zero_ne_top <| top_le_iff.mp <| h ▸ hx

-- lemma toENNReal_bot : (⊥ : EReal).toENNReal = 0 := toENNReal_of_nonpos bot_le
-- lemma toENNReal_zero : (0 : EReal).toENNReal = 0 := toENNReal_of_nonpos le_rfl

-- lemma toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x ≤ 0 := by
--   induction x <;> simp [toENNReal]

-- lemma toENNReal_ne_zero_iff {x : EReal} : x.toENNReal ≠ 0 ↔ 0 < x := by
--   simp [toENNReal_eq_zero_iff.not]

-- @[simp]
-- lemma toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x := by
--   rw [pos_iff_ne_zero, toENNReal_ne_zero_iff]

-- @[simp]
-- lemma coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
--   rw [toENNReal]
--   by_cases h_top : x = ⊤
--   · rw [if_pos h_top, h_top]
--     rfl
--   rw [if_neg h_top]
--   simp only [coe_ennreal_ofReal, ge_iff_le, hx, toReal_nonneg, max_eq_left]
--   exact coe_toReal h_top fun _ ↦ by simp_all only [le_bot_iff, zero_ne_bot]

-- lemma coe_toENNReal_eq_max {x : EReal} : x.toENNReal = max 0 x := by
--   rcases le_total 0 x with (hx | hx)
--   · rw [coe_toENNReal hx, max_eq_right hx]
--   · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

-- @[simp]
-- lemma toENNReal_coe {x : ℝ≥0∞} : (x : EReal).toENNReal = x := by
--   by_cases h_top : x = ⊤
--   · rw [h_top, coe_ennreal_top, toENNReal_top]
--   rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
--   simp [h_top]

-- @[simp] lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

-- @[simp]
-- lemma toReal_toENNReal {x : EReal} (hx : 0 ≤ x) : x.toENNReal.toReal = x.toReal := by
--   by_cases h : x = ⊤
--   · simp [h]
--   · simp [h, toReal_nonneg hx]

-- lemma toENNReal_eq_toENNReal {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
--     x.toENNReal = y.toENNReal ↔ x = y := by
--   induction x <;> induction y <;> simp_all

-- lemma toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal := by
--   induction x
--   · simp
--   · by_cases hy_top : y = ⊤
--     · simp [hy_top]
--     simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
--     exact ENNReal.ofReal_le_ofReal <| EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
--   · simp_all

-- lemma toENNReal_lt_toENNReal {x y : EReal} (hx : 0 ≤ x) (hxy : x < y) :
--     x.toENNReal < y.toENNReal :=
--   lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
--     fun h ↦ hxy.ne <| (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h

/-! ### nat coercion -/

theorem coe_coe_eq_natCast [NatCast R] (n : ℕ) : (n : R) = (n : Extended R) := rfl

theorem natCast_ne_bot [NatCast R] [BEq R] [ReflBEq R] (n : ℕ) : (n : Extended R) ≠ ⊥ := Ne.symm (ne_of_beq_false rfl)

theorem natCast_ne_top [NatCast R] [BEq R] [ReflBEq R] (n : ℕ) : (n : Extended R) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)

@[norm_cast]
theorem natCast_eq_iff [AddMonoidWithOne R] [CharZero R] {m n : ℕ} : (m : Extended R) = (n : Extended R) ↔ m = n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, Extended.coe_eq_coe_iff, Nat.cast_inj]

theorem natCast_ne_iff [AddMonoidWithOne R] [CharZero R] {m n : ℕ} : (m : Extended R) ≠ (n : Extended R) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

@[norm_cast]
theorem natCast_le_iff [PartialOrder R] [AddMonoidWithOne R] [CharZero R] [AddLeftMono R] [ZeroLEOneClass R] {m n : ℕ} : (m : Extended R) ≤ (n : Extended R) ↔ m ≤ n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, Extended.coe_le_coe_iff, Nat.cast_le]

@[norm_cast]
theorem natCast_lt_iff [PartialOrder R] [AddMonoidWithOne R] [CharZero R] [AddLeftMono R] [ZeroLEOneClass R] {m n : ℕ} : (m : Extended R) < (n : Extended R) ↔ m < n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, Extended.coe_lt_coe_iff, Nat.cast_lt]

@[simp, norm_cast]
theorem natCast_mul [PartialOrder R] [NonAssocSemiring R] [DecidableEq R] [DecidableLT R] (m n : ℕ) :
    (m * n : ℕ) = (m : Extended R) * (n : Extended R) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, Nat.cast_mul, Extended.coe_mul]

/-! ### Miscellaneous lemmas -/

theorem exists_rat_btwn_of_lt [LinearOrder R] [Field R] [IsStrictOrderedRing R] [Archimedean R] :
    ∀ {a b : Extended R}, a < b → ∃ x : ℚ, a < (x : R) ∧ ((x : R) : Extended R) < b
  | ⊤, _, h => (not_top_lt h).elim
  | (a : R), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : R), (b : R), h => by simp [exists_rat_btwn (Extended.coe_lt_coe_iff.1 h)]
  | (a : R), ⊤, _ =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : R), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

theorem lt_iff_exists_rat_btwn [LinearOrder R] [Field R] [IsStrictOrderedRing R] [Archimedean R] {a b : Extended R} :
    a < b ↔ ∃ x : ℚ, a < (x : R) ∧ ((x : R) : Extended R) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

theorem lt_iff_exists_real_btwn [LinearOrder R] [Field R] [IsStrictOrderedRing R] [Archimedean R] {a b : Extended R} : a < b ↔ ∃ x : R, a < x ∧ (x : Extended R) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : R), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/-- The set of numbers in `Extended R` that are not equal to `±∞` is equivalent to `R`. -/
def neTopBotEquivBase [Zero R] : ({⊥, ⊤}ᶜ : Set (Extended R)) ≃ R where
  toFun x := Extended.toBase x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to R
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

end Extended

-- TODO: Extended nonnegative
-- ENNRat.toERat
-- instance hasCoeENNRat

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

-- /-- Extension for the `positivity` tactic: cast from `R` to `Extended R`. -/
-- @[positivity Extended.fromBase _]
-- def evalBaseToExtended : PositivityExt where eval {u α} _zα _pα e := do
--   match u, α, e with
--   | 0, ~q(Extended R), ~q(Extended.fromBase $a) =>
--     let ra ← core q(inferInstance) q(inferInstance) a
--     assertInstancesCommute
--     match ra with
--     | .positive pa => pure (.positive q(Extended.coe_pos.2 $pa))
--     | .nonnegative pa => pure (.nonnegative q(Extended.coe_nonneg.2 $pa))
--     | .nonzero pa => pure (.nonzero q(Extended.coe_ne_zero.2 $pa))
--     | _ => pure .none
--   | _, _, _ => throwError "not Real.toEReal"

-- /-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `EReal`. -/
-- @[positivity ENNReal.toEReal _]
-- def evalExtendedNNToExtended : PositivityExt where eval {u α} _zα _pα e := do
--   match u, α, e with
--   | 0, ~q(Extended R), ~q(Extended.fromBase $a) =>
--     let ra ← core q(inferInstance) q(inferInstance) a
--     assertInstancesCommute
--     match ra with
--     | .positive pa => pure (.positive q(Extended.coe_ennreal_pos.2 $pa))
--     | .nonzero pa => pure (.positive q(Extended.coe_ennreal_pos_iff_ne_zero.2 $pa))
--     | _ => pure (.nonnegative q(Extended.coe_ennreal_nonneg $a))
--   | _, _, _ => throwError "not ENNReal.toEReal"

-- /-- Extension for the `positivity` tactic: projection from `Extended R` to `R`.

-- We prove that `Extended.toBase x` is nonnegative whenever `x` is nonnegative.
-- Since `Extended.toBase ⊤ = 0`, we cannot prove a stronger statement,
-- at least without relying on a tactic like `finiteness`. -/
-- @[positivity Extended.toBase _]
-- def evalExtendedToBase : PositivityExt where eval {u α} _zα _pα e := do
--   match u, α, e with
--   | 0, ~q(R), ~q(Extended.toBase $a) =>
--     assertInstancesCommute
--     match (← core q(inferInstance) q(inferInstance) a).toNonneg with
--     | .some pa => pure (.nonnegative q(Extended.toBase_nonneg $pa))
--     | _ => pure .none
--   | _, _, _ => throwError "not EReal.toReal"

-- /-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ≥0∞`.

-- We show that `EReal.toENNReal x` is positive whenever `x` is positive,
-- and it is nonnegative otherwise.
-- We cannot deduce any corollaries from `x ≠ 0`, since `EReal.toENNReal x = 0` for `x < 0`.
-- -/
-- @[positivity EReal.toENNReal _]
-- def evalERealToENNReal : PositivityExt where eval {u α} _zα _pα e := do
--   match u, α, e with
--   | 0, ~q(ExtendedNN R), ~q(Extended.toENNReal $a) =>
--     assertInstancesCommute
--     match ← core q(inferInstance) q(inferInstance) a with
--     | .positive pa => pure (.positive q(EReal.toENNReal_pos_iff.2 $pa))
--     | _ => pure (.nonnegative q(zero_le $e))
--   | _, _, _ => throwError "not EReal.toENNReal"

end Mathlib.Meta.Positivity
