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

open Function Set

section

/-- The extended nonnegative rational numbers. -/
def ENNRat := WithTop ℚ≥0
  deriving Zero, Top, AddCommMonoidWithOne, SemilatticeSup, DistribLattice, Nontrivial

@[inherit_doc]
scoped[ENNRat] notation "ℚ≥0∞" => ENNRat

scoped[ENNRat] notation "∞" => (⊤ : ENNRat)

namespace ENNRat

instance : OrderBot ℚ≥0∞ := inferInstanceAs (OrderBot (WithTop ℚ≥0))
instance : OrderTop ℚ≥0∞ := inferInstanceAs (OrderTop (WithTop ℚ≥0))
instance : BoundedOrder ℚ≥0∞ := inferInstanceAs (BoundedOrder (WithTop ℚ≥0))
instance : CharZero ℚ≥0∞ := inferInstanceAs (CharZero (WithTop ℚ≥0))
instance : Min ℚ≥0∞ := SemilatticeInf.toMin
instance : Max ℚ≥0∞ := SemilatticeSup.toMax

instance : DecidableEq ℚ≥0∞ := inferInstanceAs (DecidableEq (WithTop ℚ≥0))

instance : PartialOrder ℚ≥0∞ :=
  inferInstanceAs (PartialOrder (WithTop ℚ≥0))

instance : MulZeroOneClass ℚ≥0∞ :=
  inferInstanceAs (MulZeroOneClass (WithTop ℚ≥0))

instance : NoZeroDivisors ℚ≥0∞ :=
  inferInstanceAs (NoZeroDivisors (WithTop ℚ≥0))

instance : CanonicallyOrderedAdd ℚ≥0∞ :=
  inferInstanceAs (CanonicallyOrderedAdd (WithTop ℚ≥0))

instance : CommSemiring ℚ≥0∞ :=
  inferInstanceAs (CommSemiring (WithTop ℚ≥0))

instance : IsOrderedRing ℚ≥0∞ :=
  inferInstanceAs (IsOrderedRing (WithTop ℚ≥0))

instance : AddCommMonoid ℚ≥0∞ :=
  inferInstanceAs (AddCommMonoid (WithTop ℚ≥0))

instance : LinearOrder ℚ≥0∞ :=
  inferInstanceAs (LinearOrder (WithTop ℚ≥0))

instance : IsOrderedAddMonoid ℚ≥0∞ :=
  inferInstanceAs (IsOrderedAddMonoid (WithTop ℚ≥0))

instance instSub : Sub ℚ≥0∞ := inferInstanceAs (Sub (WithTop ℚ≥0))
instance : OrderedSub ℚ≥0∞ := inferInstanceAs (OrderedSub (WithTop ℚ≥0))

instance : LinearOrderedAddCommMonoidWithTop ℚ≥0∞ :=
  inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop ℚ≥0))

/-- Coercion from `ℚ≥0` to `ℚ≥0∞`. -/
@[coe, match_pattern] def ofNNRat : ℚ≥0 → ℚ≥0∞ := WithTop.some

instance : NNRatCast ℚ≥0∞ where
  nnratCast r := ofNNRat r

instance : Coe ℚ≥0 ℚ≥0∞ := ⟨ofNNRat⟩

def inv : ℚ≥0∞ → ℚ≥0∞
  | 0 => ⊤
  | ⊤ => 0
  | some q => ((q⁻¹ : ℚ≥0) : ℚ≥0∞)

instance : Inv ℚ≥0∞ := ⟨inv⟩

instance : DivInvMonoid ℚ≥0∞ where

variable {a b c d : ℚ≥0∞} {r p q : ℚ≥0} {n : ℕ}

-- TODO: add a `WithTop` instance and use it here
instance : LinearOrderedCommMonoidWithZero ℚ≥0∞ :=
  { inferInstanceAs (LinearOrderedAddCommMonoidWithTop ℚ≥0∞),
      inferInstanceAs (CommSemiring ℚ≥0∞) with
    bot_le _ := bot_le
    mul_le_mul_left := fun _ _ h c => mul_le_mul_left h c
    zero_le_one := zero_le 1 }

instance : Unique (AddUnits ℚ≥0∞) where
  default := 0
  uniq a := AddUnits.ext <| le_zero_iff.1 <| by rw [← a.add_neg]; exact le_self_add

instance : Inhabited ℚ≥0∞ := ⟨0⟩

/-- A version of `WithTop.recTopCoe` that uses `ENNRat.ofNNRat`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : ℚ≥0∞ → Sort*} (top : C ∞) (coe : ∀ x : ℚ≥0, C x) (x : ℚ≥0∞) : C x :=
  WithTop.recTopCoe top coe x

instance canLift : CanLift ℚ≥0∞ ℚ≥0 ofNNRat (· ≠ ∞) := WithTop.canLift

@[simp] theorem none_eq_top : (none : ℚ≥0∞) = ∞ := rfl

@[simp] theorem some_eq_coe (a : ℚ≥0) : (Option.some a : ℚ≥0∞) = (↑a : ℚ≥0∞) := rfl

@[simp] theorem some_eq_coe' (a : ℚ≥0) : (WithTop.some a : ℚ≥0∞) = (↑a : ℚ≥0∞) := rfl

lemma coe_injective : Injective ((↑) : ℚ≥0 → ℚ≥0∞) := WithTop.coe_injective

@[simp, norm_cast] lemma coe_inj : (p : ℚ≥0∞) = q ↔ p = q := coe_injective.eq_iff

lemma coe_ne_coe : (p : ℚ≥0∞) ≠ q ↔ p ≠ q := coe_inj.not

theorem range_coe' : range ofNNRat = Iio ∞ := WithTop.range_coe
theorem range_coe : range ofNNRat = {∞}ᶜ := (isCompl_range_some_none ℚ≥0).symm.compl_eq.symm

theorem ofNNRat_eq_NNRatCast (p : ℚ≥0) : ofNNRat p = @NNRat.cast ℚ≥0∞ _ p := rfl

theorem ofNNRat_inj {p q : ℚ≥0} : ofNNRat p = ofNNRat q ↔ p = q := WithTop.coe_inj

theorem ofNNRat_le {p q : ℚ≥0} : ofNNRat p ≤ ofNNRat q ↔ p ≤ q := WithTop.coe_le_coe

theorem ofNNRat_lt {p q : ℚ≥0} : ofNNRat p < ofNNRat q ↔ p < q := WithTop.coe_lt_coe

theorem ofNNRat_ne_top (p : ℚ≥0) : ofNNRat p ≠ ∞ := WithTop.coe_ne_top

theorem ofNNRat_lt_top (p : ℚ≥0) : ofNNRat p < ∞ := WithTop.coe_lt_top p

theorem ofNNRat_add {p q : ℚ≥0} : ofNNRat p + ofNNRat q = ofNNRat (p + q) := rfl

-- @[norm_cast]
theorem coe_nnratCast (q : ℚ≥0) : ↑(q : ℚ≥0) = (q : ℚ≥0∞) := rfl

/-- `toNNRat x` returns `x` if it is Rat, otherwise 0. -/
protected def toNNRat : ℚ≥0∞ → ℚ≥0 := WithTop.untopD 0

/-- `toRat x` returns `x` if it is Rat, `0` otherwise. -/
protected def toRat (a : ℚ≥0∞) : Rat := a.toNNRat

/-- `ofRat x` returns `x` if it is nonnegative, `0` otherwise. -/
protected def ofRat (r : Rat) : ℚ≥0∞ := r.toNNRat

@[simp, norm_cast] lemma toNNRat_coe (r : ℚ≥0) : (r : ℚ≥0∞).toNNRat = r := rfl

@[simp]
theorem coe_toNNRat : ∀ {a : ℚ≥0∞}, a ≠ ∞ → ↑a.toNNRat = a
  | ofNNRat _, _ => rfl
  | ⊤, h => (h rfl).elim

@[simp]
theorem coe_comp_toNNRat_comp {ι : Type*} {f : ι → ℚ≥0∞} (hf : ∀ x, f x ≠ ∞) :
    (fun (x : ℚ≥0) => (x : ℚ≥0∞)) ∘ ENNRat.toNNRat ∘ f = f := by
  ext x
  simp [coe_toNNRat (hf x)]

@[simp]
theorem ofRat_toRat {a : ℚ≥0∞} (h : a ≠ ∞) : ENNRat.ofRat a.toRat = a := by
  simp [ENNRat.toRat, ENNRat.ofRat, h]

@[simp]
theorem toRat_ofRat {r : ℚ} (h : 0 ≤ r) : (ENNRat.ofRat r).toRat = r :=
  max_eq_left h

theorem toRat_ofRat' {r : ℚ} : (ENNRat.ofRat r).toRat = max r 0 := rfl

theorem coe_toNNRat_le_self : ∀ {a : ℚ≥0∞}, ↑(a.toNNRat) ≤ a
  | ofNNRat r => by rfl
  | ⊤ => le_top

theorem coe_nnRat_eq (r : ℚ≥0) : (r : ℚ≥0∞) = ENNRat.ofRat r := by
  rw [ENNRat.ofRat]
  simp

theorem ofRat_eq_coe_nnRat {x : ℚ} (h : 0 ≤ x) :
    ENNRat.ofRat x = ofNNRat ⟨x, h⟩ :=
  (coe_nnRat_eq ⟨x, h⟩).symm

theorem ofNNRat_toNNRat (x : ℚ) : (Rat.toNNRat x : ℚ≥0∞) = ENNRat.ofRat x := rfl

@[simp] theorem ofRat_coe_nnRat : ENNRat.ofRat p = p := (coe_nnRat_eq p).symm

@[simp, norm_cast] theorem coe_zero : ↑(0 : ℚ≥0) = (0 : ℚ≥0∞) := rfl

@[simp, norm_cast] theorem coe_one : ↑(1 : ℚ≥0) = (1 : ℚ≥0∞) := rfl

@[simp] theorem toRat_nonneg {a : ℚ≥0∞} : 0 ≤ a.toRat := a.toNNRat.2

@[norm_cast] theorem coe_toNNRat_eq_toRat (z : ℚ≥0∞) : (z.toNNRat : ℚ) = z.toRat := rfl

@[simp] theorem toNNRat_toRat_eq (z : ℚ≥0∞) : z.toRat.toNNRat = z.toNNRat := by
  ext
  simp [coe_toNNRat_eq_toRat, Rat.toNNRat]

@[simp] theorem toNNRat_top : ∞.toNNRat = 0 := rfl

@[deprecated (since := "2025-03-20")] alias top_toNNRat := toNNRat_top

@[simp] theorem toRat_top : ∞.toRat = 0 := rfl

@[deprecated (since := "2025-03-20")] alias top_toRat := toRat_top

@[simp] theorem toRat_one : (1 : ℚ≥0∞).toRat = 1 := rfl

@[deprecated (since := "2025-03-20")] alias one_toRat := toRat_one

@[simp] theorem toNNRat_one : (1 : ℚ≥0∞).toNNRat = 1 := rfl

@[deprecated (since := "2025-03-20")] alias one_toNNRat := toNNRat_one

@[simp] theorem coe_toRat (r : ℚ≥0) : (r : ℚ≥0∞).toRat = r := rfl

@[simp] theorem toNNRat_zero : (0 : ℚ≥0∞).toNNRat = 0 := rfl

@[deprecated (since := "2025-03-20")] alias zero_toNNRat := toNNRat_zero

@[simp] theorem toRat_zero : (0 : ℚ≥0∞).toRat = 0 := rfl

@[deprecated (since := "2025-03-20")] alias zero_toRat := toRat_zero

@[simp] theorem ofRat_zero : ENNRat.ofRat (0 : ℚ) = 0 := by simp [ENNRat.ofRat]

@[simp] theorem ofRat_one : ENNRat.ofRat (1 : ℚ) = (1 : ℚ≥0∞) := by simp [ENNRat.ofRat]

theorem ofRat_toRat_le {a : ℚ≥0∞} : ENNRat.ofRat a.toRat ≤ a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofRat_toRat ha)

theorem forall_ennRat {p : ℚ≥0∞ → Prop} : (∀ a, p a) ↔ (∀ r : ℚ≥0, p r) ∧ p ∞ :=
  Option.forall.trans and_comm

theorem forall_ne_top {p : ℚ≥0∞ → Prop} : (∀ a, a ≠ ∞ → p a) ↔ ∀ r : ℚ≥0, p r :=
  Option.forall_ne_none

theorem exists_ne_top {p : ℚ≥0∞ → Prop} : (∃ a ≠ ∞, p a) ↔ ∃ r : ℚ≥0, p r :=
  Option.exists_ne_none

theorem toNNRat_eq_zero_iff (x : ℚ≥0∞) : x.toNNRat = 0 ↔ x = 0 ∨ x = ∞ :=
  WithTop.untopD_eq_self_iff

theorem toRat_eq_zero_iff (x : ℚ≥0∞) : x.toRat = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [ENNRat.toRat, toNNRat_eq_zero_iff]

theorem toNNRat_ne_zero : a.toNNRat ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toNNRat_eq_zero_iff.not.trans not_or

theorem toRat_ne_zero : a.toRat ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toRat_eq_zero_iff.not.trans not_or

theorem toNNRat_eq_one_iff (x : ℚ≥0∞) : x.toNNRat = 1 ↔ x = 1 :=
  WithTop.untopD_eq_iff.trans <| by simp

theorem toRat_eq_one_iff (x : ℚ≥0∞) : x.toRat = 1 ↔ x = 1 := by
  rw [ENNRat.toRat, ENNRat.toNNRat]
  norm_cast
  rw [WithTop.untopD_eq_iff]
  norm_num

theorem toNNRat_ne_one : a.toNNRat ≠ 1 ↔ a ≠ 1 :=
  a.toNNRat_eq_one_iff.not

theorem toRat_ne_one : a.toRat ≠ 1 ↔ a ≠ 1 :=
  a.toRat_eq_one_iff.not

-- theorem toRat_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toRat = a.toRat + b.toRat := by
--   lift a to ℚ≥0 using ha
--   lift b to ℚ≥0 using hb
--   rfl

-- theorem toRat_add_le : (a + b).toRat ≤ a.toRat + b.toRat :=
--   if ha : a = ∞ then by simp only [ha, top_add, toRat_top, zero_add, toRat_nonneg]
--   else
--     if hb : b = ∞ then by simp only [hb, add_top, toRat_top, add_zero, toRat_nonneg]
--     else le_of_eq (toRat_add ha hb)

-- @[simp]
-- theorem toRat_le_toRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toRat ≤ b.toRat ↔ a ≤ b := by
--   lift a to ℚ≥0 using ha
--   lift b to ℚ≥0 using hb
--   rw [ofNNRat_eq_NNRatCast a, coe_toRat a, ofNNRat_eq_NNRatCast b, coe_toRat b]
--   sorry
  -- rw [Rat.instNNRatCast]
  -- norm_num
  -- apply NNRat.cast_le (K := ℚ)
  -- constructor
  -- · intro h
  --   norm_cast at h
  --   -- apply (NNRat.cast_le (K := ℚ≥0∞)).mpr
  --   -- apply NNRat.cast_mono
  --   unfold instNNRatCast
  --   unfold_projs
  --   norm_num
  --   intro b1 hb
  --   use a
  --   split_ands
  --   · trivial
  --   · unfold Rat.blt
  --     norm_num
  --     split_ifs with h1
  --     · rw [h1] at hb
  --       norm_cast at hb
  --       unfold_projs at hb
  --       norm_cast at hb


        -- norm_cast at hb
        -- rw [NNRat.cast_eq_zero] at hb




-- theorem toRat_mono {a b : ℚ≥0∞} (hb : b ≠ ∞) (h : a ≤ b) : a.toRat ≤ b.toRat :=
--   (toRat_le_toRat (ne_top_of_le_ne_top hb h) hb).2 h

-- theorem toRat_mono' {a b : ℚ≥0∞} (h : a ≤ b) (ht : b = ⊤ → a = ⊤) : a.toRat ≤ b.toRat := by
--   rcases eq_or_ne a ∞ with rfl | ha
--   · exact toRat_nonneg
--   · exact toRat_mono (mt ht ha) h


@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem coe_ne_top : (r : ℚ≥0∞) ≠ ∞ := WithTop.coe_ne_top

@[simp] theorem top_ne_coe : ∞ ≠ (r : ℚ≥0∞) := WithTop.top_ne_coe

@[simp] theorem coe_lt_top : (r : ℚ≥0∞) < ∞ := WithTop.coe_lt_top r

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem ofRat_ne_top {r : ℚ} : ENNRat.ofRat r ≠ ∞ := coe_ne_top

@[simp] theorem ofRat_lt_top {r : ℚ} : ENNRat.ofRat r < ∞ := coe_lt_top

@[simp] theorem top_ne_ofRat {r : ℚ} : ∞ ≠ ENNRat.ofRat r := top_ne_coe

@[simp]
theorem ofRat_toRat_eq_iff : ENNRat.ofRat a.toRat = a ↔ a ≠ ⊤ :=
  ⟨fun h => by
    rw [← h]
    exact ofRat_ne_top, ofRat_toRat⟩

@[simp]
theorem toRat_ofRat_eq_iff {a : ℚ} : (ENNRat.ofRat a).toRat = a ↔ 0 ≤ a :=
  ⟨fun h => by
    rw [← h]
    exact toRat_nonneg, toRat_ofRat⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem zero_ne_top : 0 ≠ ∞ := coe_ne_top

@[simp] theorem top_ne_zero : ∞ ≠ 0 := top_ne_coe

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem one_ne_top : 1 ≠ ∞ := coe_ne_top

@[simp] theorem top_ne_one : ∞ ≠ 1 := top_ne_coe

@[simp] theorem zero_lt_top : 0 < ∞ := coe_lt_top

@[simp, norm_cast] theorem coe_le_coe : (↑r : ℚ≥0∞) ≤ ↑q ↔ r ≤ q := WithTop.coe_le_coe

@[simp, norm_cast] theorem coe_lt_coe : (↑r : ℚ≥0∞) < ↑q ↔ r < q := WithTop.coe_lt_coe

-- Needed until `@[gcongr]` accepts iff statements
alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe
attribute [gcongr] ENNRat.coe_le_coe_of_le

-- Needed until `@[gcongr]` accepts iff statements
alias ⟨_, coe_lt_coe_of_lt⟩ := coe_lt_coe
attribute [gcongr] ENNRat.coe_lt_coe_of_lt

theorem coe_mono : Monotone ofNNRat := fun _ _ => coe_le_coe.2

theorem coe_strictMono : StrictMono ofNNRat := fun _ _ => coe_lt_coe.2

@[simp, norm_cast] theorem coe_eq_zero : (↑r : ℚ≥0∞) = 0 ↔ r = 0 := coe_inj

@[simp, norm_cast] theorem zero_eq_coe : 0 = (↑r : ℚ≥0∞) ↔ 0 = r := coe_inj

@[simp, norm_cast] theorem coe_eq_one : (↑r : ℚ≥0∞) = 1 ↔ r = 1 := coe_inj

@[simp, norm_cast] theorem one_eq_coe : 1 = (↑r : ℚ≥0∞) ↔ 1 = r := coe_inj

@[simp, norm_cast] theorem coe_pos : 0 < (r : ℚ≥0∞) ↔ 0 < r := coe_lt_coe

theorem coe_ne_zero : (r : ℚ≥0∞) ≠ 0 ↔ r ≠ 0 := coe_eq_zero.not

lemma coe_ne_one : (r : ℚ≥0∞) ≠ 1 ↔ r ≠ 1 := coe_eq_one.not

@[simp, norm_cast] lemma coe_add (x y : ℚ≥0) : (↑(x + y) : ℚ≥0∞) = x + y := rfl

@[simp, norm_cast] lemma coe_mul (x y : ℚ≥0) : (↑(x * y) : ℚ≥0∞) = x * y := rfl

@[norm_cast] lemma coe_nsmul (n : ℕ) (x : ℚ≥0) : (↑(n • x) : ℚ≥0∞) = n • x := rfl

@[simp, norm_cast] lemma coe_pow (x : ℚ≥0) (n : ℕ) : (↑(x ^ n) : ℚ≥0∞) = x ^ n := rfl

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℚ≥0) : ℚ≥0∞) = ofNat(n) := rfl

-- TODO: add lemmas about `OfNat.ofNat` and `<`/`≤`

theorem coe_two : ((2 : ℚ≥0) : ℚ≥0∞) = 2 := rfl

theorem toNNRat_eq_toNNRat_iff (x y : ℚ≥0∞) :
    x.toNNRat = y.toNNRat ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 :=
  WithTop.untopD_eq_untopD_iff

theorem toRat_eq_toRat_iff (x y : ℚ≥0∞) :
    x.toRat = y.toRat ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  simp only [ENNRat.toRat, NNRat.coe_inj, toNNRat_eq_toNNRat_iff]

theorem toNNRat_eq_toNNRat_iff' {x y : ℚ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toNNRat = y.toNNRat ↔ x = y := by
  simp only [ENNRat.toNNRat_eq_toNNRat_iff x y, hx, hy, and_false, false_and, or_false]

theorem toRat_eq_toRat_iff' {x y : ℚ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toRat = y.toRat ↔ x = y := by
  simp only [ENNRat.toRat, NNRat.coe_inj, toNNRat_eq_toNNRat_iff' hx hy]

theorem one_lt_two : (1 : ℚ≥0∞) < 2 := Nat.one_lt_ofNat

/-- `(1 : ℚ≥0∞) ≤ 1`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_one_ennRat : Fact ((1 : ℚ≥0∞) ≤ 1) :=
  ⟨le_rfl⟩

/-- `(1 : ℚ≥0∞) ≤ 2`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_two_ennRat : Fact ((1 : ℚ≥0∞) ≤ 2) :=
  ⟨one_le_two⟩

/-- `(1 : ℚ≥0∞) ≤ ∞`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_top_ennRat : Fact ((1 : ℚ≥0∞) ≤ ∞) :=
  ⟨le_top⟩

/-- The set of numbers in `ℚ≥0∞` that are not equal to `∞` is equivalent to `ℚ≥0`. -/
def neTopEquivNNRat : { a | a ≠ ∞ } ≃ ℚ≥0 where
  toFun x := ENNRat.toNNRat x
  invFun x := ⟨x, coe_ne_top⟩
  left_inv := fun x => Subtype.eq <| coe_toNNRat x.2
  right_inv := toNNRat_coe

theorem iInf_ennRat {α : Type*} [CompleteLattice α] {f : ℚ≥0∞ → α} :
    ⨅ n, f n = (⨅ n : ℚ≥0, f n) ⊓ f ∞ :=
  (iInf_option f).trans (inf_comm _ _)

theorem iSup_ennRat {α : Type*} [CompleteLattice α] {f : ℚ≥0∞ → α} :
    ⨆ n, f n = (⨆ n : ℚ≥0, f n) ⊔ f ∞ :=
  @iInf_ennRat αᵒᵈ _ _

/-- Coercion `ℚ≥0 → ℚ≥0∞` as a `RingHom`. -/
def ofNNRatHom : ℚ≥0 →+* ℚ≥0∞ where
  toFun := some
  map_one' := coe_one
  map_mul' _ _ := coe_mul _ _
  map_zero' := coe_zero
  map_add' _ _ := coe_add _ _

@[simp] theorem coe_ofNNRatHom : ⇑ofNNRatHom = some := rfl

section Order

theorem bot_eq_zero : (⊥ : ℚ≥0∞) = 0 := rfl

-- `coe_lt_top` moved up

theorem not_top_le_coe : ¬∞ ≤ ↑r := WithTop.not_top_le_coe r

@[simp, norm_cast]
theorem one_le_coe_iff : (1 : ℚ≥0∞) ≤ ↑r ↔ 1 ≤ r := coe_le_coe

@[simp, norm_cast]
theorem coe_le_one_iff : ↑r ≤ (1 : ℚ≥0∞) ↔ r ≤ 1 := coe_le_coe

@[simp, norm_cast]
theorem coe_lt_one_iff : (↑p : ℚ≥0∞) < 1 ↔ p < 1 := coe_lt_coe

@[simp, norm_cast]
theorem one_lt_coe_iff : 1 < (↑p : ℚ≥0∞) ↔ 1 < p := coe_lt_coe

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℚ≥0) : ℚ≥0∞) = n := rfl

@[simp, norm_cast] lemma ofRat_natCast (n : ℕ) : ENNRat.ofRat n = n := by simp [ENNRat.ofRat]

@[simp] theorem ofRat_ofNat (n : ℕ) [n.AtLeastTwo] : ENNRat.ofRat ofNat(n) = ofNat(n) :=
  ofRat_natCast n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem natCast_ne_top (n : ℕ) : (n : ℚ≥0∞) ≠ ∞ := WithTop.natCast_ne_top n

@[simp] theorem natCast_lt_top (n : ℕ) : (n : ℚ≥0∞) < ∞ := WithTop.natCast_lt_top n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
lemma ofNat_ne_top {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) ≠ ∞ := natCast_ne_top n

@[simp]
lemma ofNat_lt_top {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) < ∞ := natCast_lt_top n

@[simp] theorem top_ne_natCast (n : ℕ) : ∞ ≠ n := WithTop.top_ne_natCast n

@[simp] theorem top_ne_ofNat {n : ℕ} [n.AtLeastTwo] : ∞ ≠ ofNat(n) :=
  ofNat_ne_top.symm

@[simp, norm_cast] lemma natCast_le_ofNNRat : (n : ℚ≥0∞) ≤ r ↔ n ≤ r := by simp [← coe_le_coe]
@[simp, norm_cast] lemma ofNNRat_le_natCast : r ≤ (n : ℚ≥0∞) ↔ r ≤ n := by simp [← coe_le_coe]

@[simp, norm_cast] lemma ofNNRat_add_natCast (r : ℚ≥0) (n : ℕ) : ofNNRat (r + n) = r + n := rfl
@[simp, norm_cast] lemma ofNNRat_natCast_add (n : ℕ) (r : ℚ≥0) : ofNNRat (n + r) = n + r := rfl

@[simp, norm_cast] lemma ofNNRat_sub_natCast (r : ℚ≥0) (n : ℕ) : ofNNRat (r - n) = r - n := rfl
@[simp, norm_cast] lemma ofNNRat_natCast_sub (n : ℕ) (r : ℚ≥0) : ofNNRat (n - r) = n - r := rfl

@[deprecated ofNat_ne_top (since := "2025-01-21")] lemma two_ne_top : (2 : ℚ≥0∞) ≠ ∞ := coe_ne_top
@[deprecated ofNat_lt_top (since := "2025-01-21")] lemma two_lt_top : (2 : ℚ≥0∞) < ∞ := coe_lt_top

@[simp] theorem one_lt_top : 1 < ∞ := coe_lt_top

@[simp, norm_cast]
theorem toNNRat_natCast (n : ℕ) : (n : ℚ≥0∞).toNNRat = n := by
  rw [← ENNRat.coe_natCast n, ENNRat.toNNRat_coe]

@[deprecated (since := "2025-02-19")] alias toNNRat_nat := toNNRat_natCast

theorem toNNRat_ofNat (n : ℕ) [n.AtLeastTwo] : ENNRat.toNNRat ofNat(n) = ofNat(n) :=
  toNNRat_natCast n

@[simp, norm_cast]
theorem toRat_natCast (n : ℕ) : (n : ℚ≥0∞).toRat = n := by
  rw [← ENNRat.ofRat_natCast n, ENNRat.toRat_ofRat (Nat.cast_nonneg _)]

@[deprecated (since := "2025-02-19")] alias toRat_nat := toRat_natCast

@[simp] theorem toRat_ofNat (n : ℕ) [n.AtLeastTwo] : ENNRat.toRat ofNat(n) = ofNat(n) :=
  toRat_natCast n

lemma toNNRat_natCast_eq_toNNRat (n : ℕ) :
    (n : ℚ≥0∞).toNNRat = (n : ℚ).toNNRat := by
  simp

theorem le_coe_iff : a ≤ ↑r ↔ ∃ p : ℚ≥0, a = p ∧ p ≤ r := WithTop.le_coe_iff

theorem coe_le_iff : ↑r ≤ a ↔ ∀ p : ℚ≥0, a = p → r ≤ p := WithTop.coe_le_iff

theorem lt_iff_exists_coe : a < b ↔ ∃ p : ℚ≥0, a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe

theorem toRat_le_coe_of_le_coe {a : ℚ≥0∞} {b : ℚ≥0} (h : a ≤ b) : a.toRat ≤ b := by
  lift a to ℚ≥0 using ne_top_of_le_ne_top coe_ne_top h
  simp [h, ENNRat.toRat]
  rw [ENNRat.toNNRat, ENNRat.ofNNRat, WithTop.untopD_coe]
  apply ENNRat.ofNNRat_le.mp h


@[simp] theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := max_eq_bot

theorem max_zero_left : max 0 a = a :=
  max_eq_right (zero_le a)

theorem max_zero_right : max a 0 = a :=
  max_eq_left (zero_le a)

theorem natCast_lt_coe {n : ℕ} : n < (r : ℚ≥0∞) ↔ n < r := ENNRat.coe_natCast n ▸ coe_lt_coe

theorem coe_lt_natCast {n : ℕ} : (r : ℚ≥0∞) < n ↔ r < n := coe_lt_coe

-- protected theorem exists_nat_gt {r : ℚ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
--   lift r to ℚ≥0 using h
--   rcases exists_nat_gt r with ⟨n, hn⟩
  -- exact ⟨n, coe_lt_natCast.2 hn⟩

-- @[simp]
-- theorem iUnion_Iio_coe_nat : ⋃ n : ℕ, Iio (n : ℚ≥0∞) = {∞}ᶜ := by
--   ext x
--   rw [mem_iUnion]
  -- exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNRat.exists_nat_gt⟩

-- @[simp]
-- theorem iUnion_Iic_coe_nat : ⋃ n : ℕ, Iic (n : ℚ≥0∞) = {∞}ᶜ :=
--   Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx) <|
--     iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

-- @[simp]
-- theorem iUnion_Ioc_coe_nat : ⋃ n : ℕ, Ioc a n = Ioi a \ {∞} := by
--   simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]

-- @[simp]
-- theorem iUnion_Ioo_coe_nat : ⋃ n : ℕ, Ioo a n = Ioi a \ {∞} := by
--   simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]

-- @[simp]
-- theorem iUnion_Icc_coe_nat : ⋃ n : ℕ, Icc a n = Ici a \ {∞} := by
--   simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]

-- @[simp]
-- theorem iUnion_Ico_coe_nat : ⋃ n : ℕ, Ico a n = Ici a \ {∞} := by
--   simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]

-- @[simp]
-- theorem iInter_Ici_coe_nat : ⋂ n : ℕ, Ici (n : ℚ≥0∞) = {∞} := by
--   simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

-- @[simp]
-- theorem iInter_Ioi_coe_nat : ⋂ n : ℕ, Ioi (n : ℚ≥0∞) = {∞} := by
--   simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

@[simp, norm_cast]
theorem coe_min (r p : ℚ≥0) : ((min r p : ℚ≥0) : ℚ≥0∞) = min (r : ℚ≥0∞) p := rfl

@[simp, norm_cast]
theorem coe_max (r p : ℚ≥0) : ((max r p : ℚ≥0) : ℚ≥0∞) = max (r : ℚ≥0∞) p := rfl

-- TODO:
-- theorem le_of_top_imp_top_of_toNNRat_le {a b : ℚ≥0∞} (h : a = ⊤ → b = ⊤)
--     (h_nnRat : a ≠ ⊤ → b ≠ ⊤ → a.toNNRat ≤ b.toNNRat) : a ≤ b := by
--   by_contra! hlt
--   lift b to ℚ≥0 using hlt.ne_top
--   lift a to ℚ≥0 using mt h coe_ne_top
--   refine hlt.not_ge ?_
--   simpa using h_nnRat

@[simp]
theorem abs_toRat {x : ℚ≥0∞} : |x.toRat| = x.toRat := by cases x <;> simp

end Order

section Bit

-- TODO: add lemmas about `OfNat.ofNat`

end Bit

end ENNRat

open ENNRat

namespace Set

namespace OrdConnected

variable {s : Set ℚ} {t : Set ℚ≥0} {u : Set ℚ≥0∞}

theorem preimage_coe_nnRat_ennRat (h : u.OrdConnected) : ((↑) ⁻¹' u : Set ℚ≥0).OrdConnected :=
  h.preimage_mono ENNRat.coe_mono

-- TODO: generalize to `WithTop`
theorem image_coe_nnRat_ennRat (h : t.OrdConnected) : ((↑) '' t : Set ℚ≥0∞).OrdConnected := by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases ENNRat.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNRat.coe_le_coe.1 hz.1, ENNRat.coe_le_coe.1 hz.2⟩)

-- theorem preimage_ennRat_ofRat (h : u.OrdConnected) : (ENNRat.ofRat ⁻¹' u).OrdConnected :=
--   h.preimage_coe_nnRat_ennRat.preimage_Rat_toNNRat

-- theorem image_ennRat_ofRat (h : s.OrdConnected) : (ENNRat.ofRat '' s).OrdConnected := by
--   simpa only [image_image] using h.image_Rat_toNNRat.image_coe_nnRat_ennRat

end OrdConnected

end Set

/-- While not very useful, this instance uses the same representation as `Rat.instRepr`. -/
unsafe instance : Repr ℚ≥0∞ where
  reprPrec
  | (r : ℚ≥0), p => Repr.addAppParen f!"ENNRat.ofRat ({repr r.val})" p
  | ∞, _ => "∞"

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNRat.toRat`. -/
@[positivity ENNRat.toRat _]
def evalENNRattoRat : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℚ), ~q(ENNRat.toRat $a) =>
    assertInstancesCommute
    pure (.nonnegative q(ENNRat.toRat_nonneg))
  | _, _, _ => throwError "not ENNRat.toRat"

/-- Extension for the `positivity` tactic: `ENNRat.ofNNRat`. -/
@[positivity ENNRat.ofNNRat _]
def evalENNRatOfNNRat : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℚ≥0∞), ~q(ENNRat.ofNNRat $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure <| .positive q(ENNRat.coe_pos.mpr $pa)
    | _ => pure .none
  | _, _, _ => throwError "not ENNRat.ofNNRat"

end Mathlib.Meta.Positivity
