import Flean.ERat.Basic

section

namespace ERat

/-! ### Addition -/

@[simp]
theorem add_bot (x : ERat) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
theorem bot_add (x : ERat) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
theorem add_eq_bot_iff {x y : ERat} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

lemma add_ne_bot_iff {x y : ERat} : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := WithBot.add_ne_bot

@[simp]
theorem bot_lt_add_iff {x y : ERat} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot]

@[simp]
theorem top_add_top : (⊤ : ERat) + ⊤ = ⊤ :=
  rfl

@[simp]
theorem top_add_coe (x : ℚ) : (⊤ : ERat) + x = ⊤ :=
  rfl

/-- For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equal to `⊤`. -/
@[simp]
theorem top_add_of_ne_bot {x : ERat} (h : x ≠ ⊥) : ⊤ + x = ⊤ := by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

/-- For any extended real number `x`, the sum of `⊤` and `x` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem top_add_iff_ne_bot {x : ERat} : ⊤ + x = ⊤ ↔ x ≠ ⊥ := by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | bot => contradiction
    | top => rfl
    | coe r => exact top_add_of_ne_bot h

/-- For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equal to `⊤`. -/
@[simp]
theorem add_top_of_ne_bot {x : ERat} (h : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add_of_ne_bot h]

/-- For any extended real number `x`, the sum of `x` and `⊤` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem add_top_iff_ne_bot {x : ERat} : x + ⊤ = ⊤ ↔ x ≠ ⊥ := by rw [add_comm, top_add_iff_ne_bot]

protected theorem add_pos_of_nonneg_of_pos {a b : ERat} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  -- 0 ≤ a implies a ≠ ⊥ (since ⊥ < 0)
  have ha_ne_bot : a ≠ ⊥ := fun h => (lt_of_lt_of_le bot_lt_zero (h ▸ ha)).ne rfl
  -- 0 < b implies b ≠ ⊥
  have hb_ne_bot : b ≠ ⊥ := fun h => (lt_of_lt_of_le bot_lt_zero (h ▸ hb.le)).ne rfl
  match b with
  | ⊤ => simp only [add_top_of_ne_bot ha_ne_bot, zero_lt_top]
  | ⊥ => exact (hb_ne_bot rfl).elim
  | (b' : ℚ) =>
    match a with
    | ⊤ => simp only [top_add_of_ne_bot (coe_ne_bot b'), zero_lt_top]
    | ⊥ => exact (ha_ne_bot rfl).elim
    | (a' : ℚ) =>
      have h1 : (0 : ERat) = ↑(0 : ℚ) := rfl
      rw [h1, ← coe_add, ERat.coe_lt_coe_iff]
      exact _root_.add_pos_of_nonneg_of_pos (ERat.coe_le_coe_iff.mp ha) (ERat.coe_lt_coe_iff.mp hb)

protected theorem add_pos_of_pos_of_nonneg {a b : ERat} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  add_comm a b ▸ ERat.add_pos_of_nonneg_of_pos hb ha

/-- For any two extended real numbers `a` and `b`, if both `a` and `b` are greater than `0`,
then their sum is also greater than `0`. -/
protected theorem add_pos {a b : ERat} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  ERat.add_pos_of_nonneg_of_pos ha.le hb

@[simp]
theorem coe_add_top (x : ℚ) : (x : ERat) + ⊤ = ⊤ :=
  rfl

theorem toRat_add {x y : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toRat (x + y) = toRat x + toRat y := by
  lift x to ℚ using ⟨hx, h'x⟩
  lift y to ℚ using ⟨hy, h'y⟩
  rfl

-- lemma toENNRat_add {x y : ERat} (hx : 0 ≤ x) (hy : 0 ≤ y) :
--     (x + y).toENNRat = x.toENNRat + y.toENNRat := by
--   induction x <;> induction y <;> try {· simp_all}
--   norm_cast
--   simp_rw [real_coe_toENNReal]
--   simp_all [ENNReal.ofReal_add]

-- lemma toENNReal_add_le {x y : ERat} : (x + y).toENNReal ≤ x.toENNReal + y.toENNReal := by
--   induction x <;> induction y <;> try {· simp}
--   exact ENNReal.ofReal_add_le

theorem addLECancellable_coe (x : ℚ) : AddLECancellable (x : ERat)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℚ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : ℚ), (z : ℚ), h => by
    simpa only [← coe_add, ERat.coe_le_coe_iff, add_le_add_iff_left] using h

-- TODO: add `MulLECancellable.strictMono*` etc
theorem add_lt_add_right_coe {x y : ERat} (h : x < y) (z : ℚ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge

theorem add_lt_add_left_coe {x y : ERat} (h : x < y) (z : ℚ) : (z : ERat) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z

theorem add_lt_add {x y z t : ERat} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to ℚ using ⟨h1.ne_top, hx⟩
    calc (x : ERat) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := add_le_add_left h1.le t

theorem add_lt_add_of_lt_of_le' {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to ℚ using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/-- See also `ERat.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
theorem add_lt_add_of_lt_of_le {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

theorem add_lt_top {x y : ERat} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ :=
  add_lt_add hx.lt_top hy.lt_top

lemma add_ne_top {x y : ERat} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ :=
  lt_top_iff_ne_top.mp <| add_lt_top hx hy

lemma add_ne_top_iff_ne_top₂ {x y : ERat} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  cases x <;> simp_all only [ne_eq, not_false_eq_true, top_add_of_ne_bot, not_true_eq_false,
    IsEmpty.forall_iff]
  cases y <;> simp_all only [not_false_eq_true, ne_eq, add_top_of_ne_bot, not_true_eq_false,
    coe_ne_top, and_self, implies_true]

lemma add_ne_top_iff_ne_top_left {x y : ERat} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  cases x <;> simp [add_ne_top_iff_ne_top₂, hy, hy']

lemma add_ne_top_iff_ne_top_right {x y : ERat} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) :
    x + y ≠ ⊤ ↔ y ≠ ⊤ := add_comm x y ▸ add_ne_top_iff_ne_top_left hx hx'

lemma add_ne_top_iff_of_ne_bot {x y : ERat} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  induction x <;> simp_all
  induction y <;> simp_all

lemma add_ne_top_iff_of_ne_bot_of_ne_top {x y : ERat} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  induction x <;> simp [add_ne_top_iff_of_ne_bot, hy, hy']

/-- We do not have a notion of `LinearOrderedAddCommMonoidWithBot` but we can at least make
the order dual of the extended reals into a `LinearOrderedAddCommMonoidWithTop`. -/
instance : LinearOrderedAddCommMonoidWithTop ERatᵒᵈ where
  le_top := by simp
  top_add' := by
    rw [OrderDual.forall]
    intro x
    rw [← OrderDual.toDual_bot, ← toDual_add, bot_add, OrderDual.toDual_bot]

/-! ### Negation -/

/-- negation on `ERat` -/
protected def neg : ERat → ERat
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℚ) => (-x : ℚ)

instance : Neg ERat := ⟨ERat.neg⟩

instance : SubNegZeroMonoid ERat where
  neg_zero := congr_arg Rat.toERat neg_zero
  zsmul := zsmulRec

@[simp]
theorem neg_top : -(⊤ : ERat) = ⊥ :=
  rfl

@[simp]
theorem neg_bot : -(⊥ : ERat) = ⊤ :=
  rfl

@[simp, norm_cast] theorem coe_neg (x : ℚ) : (↑(-x) : ERat) = -↑x := rfl

@[simp, norm_cast] theorem coe_sub (x y : ℚ) : (↑(x - y) : ERat) = x - y := by rw [sub_eq_add_neg, coe_add, coe_neg, ← sub_eq_add_neg]

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℚ) : (↑(n • x) : ERat) = n • (x : ERat) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℚ →+ ERat) coe_neg _ _

instance : InvolutiveNeg ERat where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℚ) => congr_arg Rat.toERat (neg_neg a)

@[simp]
theorem toRat_neg : ∀ {a : ERat}, toRat (-a) = -toRat a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℚ) => rfl

@[simp]
theorem neg_eq_top_iff {x : ERat} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_bot_iff {x : ERat} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_zero_iff {x : ERat} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

theorem neg_strictAnti : StrictAnti (- · : ERat → ERat) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

@[simp] theorem neg_le_neg_iff {a b : ERat} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_ge

@[simp] theorem neg_lt_neg_iff {a b : ERat} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_gt

/-- `-a ≤ b` if and only if `-b ≤ a` on `ERat`. -/
protected theorem neg_le {a b : ERat} : -a ≤ b ↔ -b ≤ a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `-a ≤ b` then `-b ≤ a` on `ERat`. -/
protected theorem neg_le_of_neg_le {a b : ERat} (h : -a ≤ b) : -b ≤ a := ERat.neg_le.mp h

/-- `a ≤ -b` if and only if `b ≤ -a` on `ERat`. -/
protected theorem le_neg {a b : ERat} : a ≤ -b ↔ b ≤ -a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `a ≤ -b` then `b ≤ -a` on `ERat`. -/
protected theorem le_neg_of_le_neg {a b : ERat} (h : a ≤ -b) : b ≤ -a := ERat.le_neg.mp h

/-- `-a < b` if and only if `-b < a` on `ERat`. -/
theorem neg_lt_comm {a b : ERat} : -a < b ↔ -b < a := by rw [← neg_lt_neg_iff, neg_neg]

@[deprecated (since := "2024-11-19")] alias neg_lt_iff_neg_lt := neg_lt_comm

/-- If `-a < b` then `-b < a` on `ERat`. -/
protected theorem neg_lt_of_neg_lt {a b : ERat} (h : -a < b) : -b < a := neg_lt_comm.mp h

/-- `-a < b` if and only if `-b < a` on `ERat`. -/
theorem lt_neg_comm {a b : ERat} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff, neg_neg]

@[simp] protected theorem neg_lt_zero {a : ERat} : -a < 0 ↔ 0 < a := by rw [neg_lt_comm, neg_zero]
@[simp] protected theorem neg_le_zero {a : ERat} : -a ≤ 0 ↔ 0 ≤ a := by rw [ERat.neg_le, neg_zero]
@[simp] protected theorem neg_pos {a : ERat} : 0 < -a ↔ a < 0 := by rw [lt_neg_comm, neg_zero]
@[simp] protected theorem neg_nonneg {a : ERat} : 0 ≤ -a ↔ a ≤ 0 := by rw [ERat.le_neg, neg_zero]

/-- If `a < -b` then `b < -a` on `ERat`. -/
protected theorem lt_neg_of_lt_neg {a b : ERat} (h : a < -b) : b < -a := lt_neg_comm.mp h

/-- Negation as an order reversing isomorphism on `ERat`. -/
def negOrderIso : ERat ≃o ERatᵒᵈ :=
  { Equiv.neg ERat with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

lemma neg_add {x y : ERat} (h1 : x ≠ ⊥ ∨ y ≠ ⊤) (h2 : x ≠ ⊤ ∨ y ≠ ⊥) :
    - (x + y) = - x - y := by
  induction x <;> induction y <;> try tauto
  rw [← coe_add, ← coe_neg, ← coe_neg, ← coe_sub, neg_add']

lemma neg_sub {x y : ERat} (h1 : x ≠ ⊥ ∨ y ≠ ⊥) (h2 : x ≠ ⊤ ∨ y ≠ ⊤) :
    - (x - y) = - x + y := by
  rw [sub_eq_add_neg, neg_add _ _, sub_eq_add_neg, neg_neg] <;> simp_all

-- /-- Induction principle for `ERat`s splitting into cases `↑(x : ℚ≥0∞)` and `-↑(x : ℚ≥0∞)`.
-- In the latter case, we additionally assume `0 < x`. -/
-- @[elab_as_elim]
-- def recENNReal {motive : ERat → Sort*} (coe : ∀ x : ℚ≥0∞, motive x)
--     (neg_coe : ∀ x : ℚ≥0∞, 0 < x → motive (-x)) (x : ERat) : motive x :=
--   if hx : 0 ≤ x then coe_toENNReal hx ▸ coe _
--   else
--     haveI H₁ : 0 < -x := by simpa using hx
--     haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
--     H₂ ▸ neg_coe _ <| by positivity

-- @[simp]
-- theorem recENNReal_coe_ennreal {motive : ERat → Sort*} (coe : ∀ x : ℚ≥0∞, motive x)
--     (neg_coe : ∀ x : ℚ≥0∞, 0 < x → motive (-x)) (x : ℚ≥0∞) : recENNReal coe neg_coe x = coe x := by
--   suffices ∀ y : ERat, x = y → (recENNReal coe neg_coe y : motive y) ≍ coe x from
--     heq_iff_eq.mp (this x rfl)
--   intro y hy
--   have H₁ : 0 ≤ y := hy ▸ coe_ennreal_nonneg x
--   obtain rfl : y.toENNReal = x := by simp [← hy]
--   simp [recENNReal, H₁]

-- proof_wanted recENNReal_neg_coe_ennreal {motive : ERat → Sort*} (coe : ∀ x : ℚ≥0∞, motive x)
--     (neg_coe : ∀ x : ℚ≥0∞, 0 < x → motive (-x)) {x : ℚ≥0∞} (hx : 0 < x) :
--     recENNReal coe neg_coe (-x) = neg_coe x hx

/-!
### Subtraction

Subtraction on `ERat` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ERat`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
theorem bot_sub (x : ERat) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
theorem sub_top (x : ERat) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
theorem top_sub_bot : (⊤ : ERat) - ⊥ = ⊤ :=
  rfl

@[simp]
theorem top_sub_coe (x : ℚ) : (⊤ : ERat) - x = ⊤ :=
  rfl

@[simp]
theorem coe_sub_bot (x : ℚ) : (x : ERat) - ⊥ = ⊤ :=
  rfl

@[simp]
lemma sub_bot {x : ERat} (h : x ≠ ⊥) : x - ⊥ = ⊤ := by
  cases x <;> tauto

@[simp]
lemma top_sub {x : ERat} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  cases x <;> tauto

@[simp]
lemma sub_self {x : ERat} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) : x - x = 0 := by
  cases x <;> simp_all [← coe_sub]

lemma sub_self_le_zero {x : ERat} : x - x ≤ 0 := by
  cases x <;> simp

lemma sub_nonneg {x y : ERat} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    0 ≤ x - y ↔ y ≤ x := by
  cases x <;> cases y <;> simp_all [← ERat.coe_sub]

lemma sub_nonpos {x y : ERat} : x - y ≤ 0 ↔ x ≤ y := by
  cases x <;> cases y <;> simp [← ERat.coe_sub]

lemma sub_pos {x y : ERat} : 0 < x - y ↔ y < x := by
  cases x <;> cases y <;> simp [← ERat.coe_sub]

lemma sub_neg {x y : ERat} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    x - y < 0 ↔ x < y := by
  cases x <;> cases y <;> simp_all [← ERat.coe_sub]

theorem sub_le_sub {x y z t : ERat} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')

theorem sub_lt_sub_of_lt_of_le {x y z t : ERat} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

-- theorem coe_real_ERat_eq_coe_toNNReal_sub_coe_toNNReal (x : ℚ) :
--     (x : ERat) = Real.toNNReal x - Real.toNNReal (-x) := by
--   rcases le_total 0 x with (h | h)
--   · lift x to ℚ≥0 using h
--     rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg), Real.toNNReal_coe, ENNReal.coe_zero,
--       coe_ennreal_zero, sub_zero]
--     rfl
--   · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_nnreal_eq_coe_real,
--       Real.coe_toNNReal, zero_sub, coe_neg, neg_neg]
--     exact neg_nonneg.2 h

theorem toRat_sub {x y : ERat} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toRat (x - y) = toRat x - toRat y := by
  lift x to ℚ using ⟨hx, h'x⟩
  lift y to ℚ using ⟨hy, h'y⟩
  rw [toRat_coe, toRat_coe, ← coe_sub, toRat_coe]

-- lemma toENNReal_sub {x y : ERat} (hy : 0 ≤ y) :
--     (x - y).toENNReal = x.toENNReal - y.toENNReal := by
--   induction x <;> induction y <;> try {· simp_all [zero_tsub, ENNReal.sub_top]}
--   rename_i x y
--   by_cases hxy : x ≤ y
--   · rw [toENNReal_of_nonpos <| sub_nonpos.mpr <| ERat.coe_le_coe_iff.mpr hxy]
--     exact (tsub_eq_zero_of_le <| toENNReal_le_toENNReal <| ERat.coe_le_coe_iff.mpr hxy).symm
--   · rw [toENNReal_of_ne_top (ne_of_beq_false rfl).symm, ← coe_sub, toReal_coe,
--       ofReal_sub x (ERat.coe_nonneg.mp hy)]
--     simp

lemma add_sub_cancel_right {a : ERat} {b : ℚ} : a + b - b = a := by
  cases a <;> norm_cast
  exact _root_.add_sub_cancel_right _ _

lemma add_sub_cancel_left {a : ERat} {b : ℚ} : b + a - b = a := by
  rw [add_comm, ERat.add_sub_cancel_right]

lemma sub_add_cancel {a : ERat} {b : ℚ} : a - b + b = a := by
  rw [add_comm, ← add_sub_assoc, add_sub_cancel_left]

lemma sub_add_cancel_right {a : ERat} {b : ℚ} : b - (a + b) = -a := by
  cases a <;> norm_cast
  exact _root_.sub_add_cancel_right _ _

lemma sub_add_cancel_left {a : ERat} {b : ℚ} : b - (b + a) = -a := by
  rw [add_comm, sub_add_cancel_right]

lemma le_sub_iff_add_le {a b c : ERat} (hb : b ≠ ⊥ ∨ c ≠ ⊥) (ht : b ≠ ⊤ ∨ c ≠ ⊤) :
    a ≤ c - b ↔ a + b ≤ c := by
  induction b with
  | bot =>
    simp only [ne_eq, not_true_eq_false, false_or] at hb
    simp only [sub_bot hb, le_top, add_bot, bot_le]
  | coe b =>
    rw [← (addLECancellable_coe b).add_le_add_iff_right, sub_add_cancel]
  | top =>
    simp only [ne_eq, not_true_eq_false, false_or, sub_top, le_bot_iff] at ht ⊢
    refine ⟨fun h ↦ h ▸ (bot_add ⊤).symm ▸ bot_le, fun h ↦ ?_⟩
    by_contra ha
    exact (h.trans_lt (Ne.lt_top ht)).ne (add_top_iff_ne_bot.2 ha)

lemma sub_le_iff_le_add {a b c : ERat} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    a - b ≤ c ↔ a ≤ c + b := by
  suffices a + (-b) ≤ c ↔ a ≤ c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa

protected theorem lt_sub_iff_add_lt {a b c : ERat} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    c < a - b ↔ c + b < a :=
  lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)

theorem sub_le_of_le_add {a b c : ERat} (h : a ≤ b + c) : a - c ≤ b := by
  induction c with
  | bot => rw [add_bot, le_bot_iff] at h; simp only [h, bot_sub, bot_le]
  | coe c => exact (sub_le_iff_le_add (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => simp only [sub_top, bot_le]

/-- See also `ERat.sub_le_of_le_add`. -/
theorem sub_le_of_le_add' {a b c : ERat} (h : a ≤ b + c) : a - b ≤ c :=
  sub_le_of_le_add (add_comm b c ▸ h)

lemma add_le_of_le_sub {a b c : ERat} (h : a ≤ b - c) : a + c ≤ b := by
  rw [← neg_neg c]
  exact sub_le_of_le_add h

lemma sub_lt_iff {a b c : ERat} (h₁ : b ≠ ⊥ ∨ c ≠ ⊥) (h₂ : b ≠ ⊤ ∨ c ≠ ⊤) :
    c - b < a ↔ c < a + b :=
  lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)

lemma add_lt_of_lt_sub {a b c : ERat} (h : a < b - c) : a + c < b := by
  contrapose! h
  exact sub_le_of_le_add h

lemma sub_lt_of_lt_add {a b c : ERat} (h : a < b + c) : a - c < b :=
  add_lt_of_lt_sub <| by rwa [sub_eq_add_neg, neg_neg]

/-- See also `ERat.sub_lt_of_lt_add`. -/
lemma sub_lt_of_lt_add' {a b c : ERat} (h : a < b + c) : a - b < c :=
  sub_lt_of_lt_add <| by rwa [add_comm]

/-! ### Addition and order -/

-- lemma le_of_forall_lt_iff_le {x y : ERat} : (∀ z : ℚ, x < z → y ≤ z) ↔ y ≤ x := by
--   refine ⟨fun h ↦ WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z ↦ h.trans x_z.le⟩
--   rw [WithTop.forall]
--   aesop

-- lemma ge_of_forall_gt_iff_ge {x y : ERat} : (∀ z : ℚ, z < y → z ≤ x) ↔ y ≤ x := by
--   refine ⟨fun h ↦ WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z ↦ x_z.le.trans h⟩
--   rw [WithTop.forall]
--   aesop

-- private lemma exists_lt_add_left {a b c : ERat} (hc : c < a + b) : ∃ a' < a, c < a' + b := by
--   obtain ⟨a', hc', ha'⟩ := exists_between (sub_lt_of_lt_add hc)
--   refine ⟨a', ha', (sub_lt_iff (.inl ?_) (.inr hc.ne_top)).1 hc'⟩
--   contrapose! hc
--   exact hc ▸ (add_bot a).symm ▸ bot_le

-- private lemma exists_lt_add_right {a b c : ERat} (hc : c < a + b) : ∃ b' < b, c < a + b' := by
--   simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc

-- lemma add_le_of_forall_lt {a b c : ERat} (h : ∀ a' < a, ∀ b' < b, a' + b' ≤ c) : a + b ≤ c := by
--   refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
--   obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
--   obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
--   exact hd.le.trans (h _ ha' _ hb')

-- lemma le_add_of_forall_gt {a b c : ERat} (h₁ : a ≠ ⊥ ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ ⊥)
--     (h : ∀ a' > a, ∀ b' > b, c ≤ a' + b') : c ≤ a + b := by
--   rw [← neg_le_neg_iff, neg_add h₁ h₂]
--   refine add_le_of_forall_lt fun a' ha' b' hb' ↦ ERat.le_neg_of_le_neg ?_
--   rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
--   exact h _ (ERat.lt_neg_of_lt_neg ha') _ (ERat.lt_neg_of_lt_neg hb')

-- @[deprecated (since := "2024-11-19")] alias top_add_le_of_forall_add_le := add_le_of_forall_lt
-- @[deprecated (since := "2024-11-19")] alias add_le_of_forall_add_le := add_le_of_forall_lt
-- @[deprecated (since := "2024-11-19")] alias le_add_of_forall_le_add := le_add_of_forall_gt

-- lemma _root_.ENNReal.toERat_sub {x y : ℚ≥0∞} (hy_top : y ≠ ∞) (h_le : y ≤ x) :
--     (x - y).toERat = x.toERat - y.toERat := by
--   lift y to ℚ≥0 using hy_top
--   cases x with
--   | top => simp [coe_nnreal_eq_coe_real]
--   | coe x =>
--     simp only [coe_nnreal_eq_coe_real, ← ENNReal.coe_sub, NNReal.coe_sub (mod_cast h_le), coe_sub]

/-! ### Multiplication -/

@[simp] lemma top_mul_top : (⊤ : ERat) * ⊤ = ⊤ := rfl

@[simp] lemma top_mul_bot : (⊤ : ERat) * ⊥ = ⊥ := rfl

@[simp] lemma bot_mul_top : (⊥ : ERat) * ⊤ = ⊥ := rfl

@[simp] lemma bot_mul_bot : (⊥ : ERat) * ⊥ = ⊤ := rfl

lemma coe_mul_top_of_pos {x : ℚ} (h : 0 < x) : (x : ERat) * ⊤ = ⊤ :=
  if_pos h

lemma coe_mul_top_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊤ = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

lemma top_mul_coe_of_pos {x : ℚ} (h : 0 < x) : (⊤ : ERat) * x = ⊤ :=
  if_pos h

lemma top_mul_coe_of_neg {x : ℚ} (h : x < 0) : (⊤ : ERat) * x = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

lemma mul_top_of_pos : ∀ {x : ERat}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℚ), h => coe_mul_top_of_pos (ERat.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_top_of_neg : ∀ {x : ERat}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℚ), h => coe_mul_top_of_neg (ERat.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma top_mul_of_pos {x : ERat} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [ERat.mul_comm]
  exact mul_top_of_pos h

lemma top_mul_of_neg {x : ERat} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [ERat.mul_comm]
  exact mul_top_of_neg h

-- lemma top_mul_coe_ennreal {x : ℚ≥0∞} (hx : x ≠ 0) : ⊤ * (x : ERat) = ⊤ :=
--   top_mul_of_pos <| coe_ennreal_pos.mpr <| pos_iff_ne_zero.mpr hx

-- lemma coe_ennreal_mul_top {x : ℚ≥0∞} (hx : x ≠ 0) : (x : ERat) * ⊤ = ⊤ := by
--   rw [ERat.mul_comm, top_mul_coe_ennreal hx]

lemma coe_mul_bot_of_pos {x : ℚ} (h : 0 < x) : (x : ERat) * ⊥ = ⊥ :=
  if_pos h

lemma coe_mul_bot_of_neg {x : ℚ} (h : x < 0) : (x : ERat) * ⊥ = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

lemma bot_mul_coe_of_pos {x : ℚ} (h : 0 < x) : (⊥ : ERat) * x = ⊥ :=
  if_pos h

lemma bot_mul_coe_of_neg {x : ℚ} (h : x < 0) : (⊥ : ERat) * x = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

lemma mul_bot_of_pos : ∀ {x : ERat}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℚ), h => coe_mul_bot_of_pos (ERat.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_bot_of_neg : ∀ {x : ERat}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℚ), h => coe_mul_bot_of_neg (ERat.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma bot_mul_of_pos {x : ERat} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [ERat.mul_comm]
  exact mul_bot_of_pos h

lemma bot_mul_of_neg {x : ERat} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [ERat.mul_comm]
  exact mul_bot_of_neg h

lemma toRat_mul {x y : ERat} : toRat (x * y) = toRat x * toRat y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, ERat.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]

instance : NoZeroDivisors ERat where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← ERat.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [ERat.bot_mul_of_neg, ERat.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [ERat.mul_bot_of_pos, ERat.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [ERat.mul_top_of_neg, ERat.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [ERat.top_mul_of_pos, ERat.top_mul_of_neg, h]

lemma mul_pos_iff {a b : ERat} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using ERat.induction₂_symm with
  | symm h => simp [ERat.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [ERat.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, ERat.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, ERat.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, ERat.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_nonneg_iff {a b : ERat} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto

protected lemma mul_nonneg {a b : ERat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg_iff.mpr <| .inl ⟨ha, hb⟩

/-- The product of two positive extended real numbers is positive. -/
protected lemma mul_pos {a b : ERat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)

/-- Induct on two ERats by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
lemma induction₂_neg_left {P : ERat → ERat → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℚ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : ℚ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℚ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℚ, P x y) : ∀ x y, P x y :=
  have : ∀ y, (∀ x : ℚ, 0 < x → P x y) → ∀ x : ℚ, x < 0 → P x y := fun _ h x hx =>
    neg_neg (x : ERat) ▸ neg_left <| h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two ERats by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
lemma induction₂_symm_neg {P : ERat → ERat → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℚ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℚ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℚ, 0 < y → P x y) → ∀ y : ℚ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : ERat) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

protected lemma neg_mul (x y : ERat) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]

instance : HasDistribNeg ERat where
  neg_mul := ERat.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    exact y.neg_mul x

lemma mul_neg_iff {a b : ERat} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm, ← mul_neg a, mul_pos_iff, neg_lt_comm, lt_neg_comm, neg_zero]

lemma mul_nonpos_iff {a b : ERat} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  nth_rw 1 [← neg_zero]
  rw [ERat.le_neg, ← mul_neg, mul_nonneg_iff, ERat.neg_le, ERat.le_neg, neg_zero]

lemma mul_eq_top (a b : ERat) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using ERat.induction₂_symm with
  | symm h =>
    rw [ERat.mul_comm, h]
    refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩ <;>
    cases H with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  | top_top => simp
  | top_pos _ hx => simp [ERat.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, ERat.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, ERat.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simpa only [ERat.coe_ne_bot, ERat.coe_neg', false_and, and_false, ERat.coe_ne_top,
      ERat.coe_pos, or_self, iff_false, ERat.coe_mul] using ERat.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, ERat.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_ne_top (a b : ERat) :
    a * b ≠ ⊤ ↔ (a ≠ ⊥ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  set_option push_neg.use_distrib true in push_neg
  rfl

lemma mul_eq_bot (a b : ERat) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  rw [← neg_eq_top_iff, ← ERat.neg_mul, mul_eq_top, neg_eq_bot_iff, neg_eq_top_iff,
    neg_lt_comm, lt_neg_comm, neg_zero]
  tauto

lemma mul_ne_bot (a b : ERat) :
    a * b ≠ ⊥ ↔ (a ≠ ⊥ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  set_option push_neg.use_distrib true in push_neg
  rfl

-- /-- `ERat.toENNReal` is multiplicative. For the version with the nonnegativity
-- hypothesis on the second variable, see `ERat.toENNReal_mul'`. -/
-- lemma toENNReal_mul {x y : ERat} (hx : 0 ≤ x) :
--     (x * y).toENNReal = x.toENNReal * y.toENNReal := by
--   induction x <;> induction y
--     <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
--   · rcases eq_or_lt_of_le hx with (hx | hx)
--     · simp [← hx]
--     · simp_all [mul_top_of_pos hx]
--   · rename_i a
--     rcases lt_trichotomy a 0 with (ha | ha | ha)
--     · simp_all [le_of_lt, top_mul_of_neg (ERat.coe_neg'.mpr ha)]
--     · simp [ha]
--     · simp_all [top_mul_of_pos (ERat.coe_pos.mpr ha)]

-- /-- `ERat.toENNReal` is multiplicative. For the version with the nonnegativity
-- hypothesis on the first variable, see `ERat.toENNReal_mul`. -/
-- lemma toENNReal_mul' {x y : ERat} (hy : 0 ≤ y) :
--     (x * y).toENNReal = x.toENNReal * y.toENNReal := by
--   rw [ERat.mul_comm, toENNReal_mul hy, mul_comm]

-- Helper for distributivity: if a + b = 0 with a, b ≥ 0 then both are 0
private lemma add_eq_zero_of_nonneg {a b : ERat} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 0) :
    a = 0 ∧ b = 0 := by
  constructor
  · by_contra h
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    have : 0 < a + b := ERat.add_pos_of_pos_of_nonneg hapos hb
    exact (this.ne' hab).elim
  · by_contra h
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
    have : 0 < a + b := ERat.add_pos_of_nonneg_of_pos ha hbpos
    exact (this.ne' hab).elim

-- The key distributivity lemma: (a + b) * c = a * c + b * c when a, b ≥ 0
lemma right_distrib_of_nonneg {a b c : ERat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * c = a * c + b * c := by
  induction c using ERat.rec with
  | bot =>
    by_cases hab : a + b = 0
    · obtain ⟨ha0, hb0⟩ := add_eq_zero_of_nonneg ha hb hab
      simp [ha0, hb0]
    · have hab_pos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
      rw [mul_bot_of_pos hab_pos]
      by_cases ha0 : a = 0
      · simp only [ha0, zero_mul, zero_add]
        have hb_pos : 0 < b := by rwa [ha0, zero_add] at hab_pos
        rw [mul_bot_of_pos hb_pos]
      · rw [mul_bot_of_pos (lt_of_le_of_ne ha (Ne.symm ha0)), bot_add]
  | coe c =>
    -- Case split on a and b being ⊤ or finite
    rcases eq_or_ne a ⊤ with rfl | ha'
    · -- a = ⊤
      have hb_ne_bot : b ≠ ⊥ := ne_bot_of_le_ne_bot (ne_of_gt bot_lt_zero) hb
      rw [top_add_of_ne_bot hb_ne_bot]
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · simp only [top_mul_coe_of_neg hc]
        symm; exact bot_add (b * c)
      · simp only [coe_zero, mul_zero, add_zero]
      · simp only [top_mul_coe_of_pos hc]
        have hc_nonneg : (0 : ERat) ≤ c := le_of_lt (ERat.coe_pos.mpr hc)
        have hmul_ne_bot : b * ↑c ≠ ⊥ := (mul_ne_bot b c).mpr ⟨Or.inl hb_ne_bot, Or.inr (coe_ne_bot c), Or.inr hc_nonneg, Or.inl hb⟩
        symm; exact top_add_of_ne_bot hmul_ne_bot
    · rcases eq_or_ne b ⊤ with rfl | hb'
      · -- b = ⊤
        have ha_ne_bot : a ≠ ⊥ := ne_bot_of_le_ne_bot (ne_of_gt bot_lt_zero) ha
        rw [add_top_of_ne_bot ha_ne_bot]
        rcases lt_trichotomy c 0 with hc | rfl | hc
        · simp only [top_mul_coe_of_neg hc]
          symm; exact add_bot (a * c)
        · simp only [coe_zero, mul_zero, add_zero]
        · simp only [top_mul_coe_of_pos hc]
          -- Goal is ⊤ = a * c + ⊤, use add_top_of_ne_bot
          have hc_nonneg : (0 : ERat) ≤ c := le_of_lt (ERat.coe_pos.mpr hc)
          have hmul_ne_bot : a * ↑c ≠ ⊥ := (mul_ne_bot a c).mpr ⟨Or.inl ha_ne_bot, Or.inr (coe_ne_bot c), Or.inr hc_nonneg, Or.inl ha⟩
          symm; exact add_top_of_ne_bot hmul_ne_bot
      · -- Both a and b are finite
        have hab : a ≠ ⊥ := ne_bot_of_le_ne_bot (ne_of_gt bot_lt_zero) ha
        have hbb : b ≠ ⊥ := ne_bot_of_le_ne_bot (ne_of_gt bot_lt_zero) hb
        lift a to ℚ using ⟨ha', hab⟩
        lift b to ℚ using ⟨hb', hbb⟩
        simp only [← coe_add, ← coe_mul, add_mul]
  | top =>
    by_cases hab : a + b = 0
    · obtain ⟨ha0, hb0⟩ := add_eq_zero_of_nonneg ha hb hab
      simp [ha0, hb0]
    · have hab_pos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
      rw [mul_top_of_pos hab_pos]
      by_cases ha0 : a = 0
      · simp only [ha0, zero_mul, zero_add]
        have hb_pos : 0 < b := by rwa [ha0, zero_add] at hab_pos
        rw [mul_top_of_pos hb_pos]
      · rw [mul_top_of_pos (lt_of_le_of_ne ha (Ne.symm ha0))]
        have hb_ne_bot : b ≠ ⊥ := ne_bot_of_le_ne_bot (ne_of_gt bot_lt_zero) hb
        have : b * ⊤ ≠ ⊥ := (mul_ne_bot b ⊤).mpr ⟨Or.inl hb_ne_bot, Or.inr top_ne_bot, Or.inr le_top, Or.inl hb⟩
        symm; exact top_add_of_ne_bot this

lemma left_distrib_of_nonneg {a b c : ERat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [ERat.mul_comm]; nth_rewrite 2 [ERat.mul_comm]; nth_rewrite 3 [ERat.mul_comm]
  exact right_distrib_of_nonneg ha hb

-- lemma left_distrib_of_nonneg_of_ne_top {x : ERat} (hx_nonneg : 0 ≤ x)
--     (hx_ne_top : x ≠ ⊤) (y z : ERat) :
--     x * (y + z) = x * y + x * z := by
--   cases hx_nonneg.eq_or_lt with
--   | inl hx0 => rw [← hx0, zero_mul, zero_mul, zero_mul, zero_add]
--   | inr hx0 =>
--   lift x to ℚ using ⟨hx_ne_top, hx0.ne_bot⟩
--   cases y <;> cases z <;>
--     simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul];
--     rw_mod_cast [mul_add]

-- lemma right_distrib_of_nonneg_of_ne_top {x : ERat} (hx_nonneg : 0 ≤ x)
--     (hx_ne_top : x ≠ ⊤) (y z : ERat) :
--     (y + z) * x = y * x + z * x := by
--   simpa only [ERat.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

-- @[simp]
-- lemma nsmul_eq_mul (n : ℕ) (x : ERat) : n • x = n * x := by
--   induction n with
--   | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
--   | succ n ih =>
--     rw [succ_nsmul, ih, Nat.cast_succ]
--     convert (ERat.right_distrib_of_nonneg _ _).symm <;> simp

end ERat

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: sum of two `ERat`s. -/
@[positivity (_ + _ : ERat)]
def evalERatAdd : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ERat), ~q($a + $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.positive q(ERat.add_pos_of_pos_of_nonneg $pa $pb))
      | _ => pure .none
    | .nonnegative pa =>
      match ← core zα pα b with
      | .positive pb => pure (.positive q(ERat.add_pos_of_nonneg_of_pos $pa $pb))
      | .nonnegative pb => pure (.nonnegative q(add_nonneg $pa $pb))
      | _ => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a sum of 2 `ERat`s"

/-- Extension for the `positivity` tactic: product of two `ERat`s. -/
@[positivity (_ * _ : ERat)]
def evalERatMul : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ERat), ~q($a * $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match ← core zα pα b with
      | .positive pb => pure <| .positive q(ERat.mul_pos $pa $pb)
      | .nonnegative pb => pure <| .nonnegative q(ERat.mul_nonneg (le_of_lt $pa) $pb)
      | .nonzero pb => pure <| .nonzero q(mul_ne_zero (ne_of_gt $pa) $pb)
      | _ => pure .none
    | .nonnegative pa =>
      match (← core zα pα b).toNonneg with
      | .some pb => pure (.nonnegative q(ERat.mul_nonneg $pa $pb))
      | .none => pure .none
    | .nonzero pa =>
      match (← core zα pα b).toNonzero with
      | .some pb => pure (.nonzero q(mul_ne_zero $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a product of 2 `ERat`s"

end Mathlib.Meta.Positivity
