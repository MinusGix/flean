import Flean.ERat.Basic
import Flean.ERat.Operations
import Flean.ENNRat.Operations
import Flean.ENNRat.Rat
import Flean.ENNRat.Inv
import Mathlib.Data.Sign.Defs
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.Archimedean.Basic

open Set SignType ENNRat

section
namespace ERat

-- Helper lemmas for coercion from ENNRat to ERat
@[simp, norm_cast]
theorem coe_ennRat_zero : ((0 : ℚ≥0∞) : ERat) = 0 := rfl

@[simp, norm_cast]
theorem coe_ennRat_one : ((1 : ℚ≥0∞) : ERat) = 1 := rfl

@[simp, norm_cast]
theorem coe_ennRat_top : ((⊤ : ℚ≥0∞) : ERat) = ⊤ := rfl

@[simp, norm_cast]
theorem coe_ennRat_mul (x y : ℚ≥0) : ((x * y : ℚ≥0∞) : ERat) = (x : ERat) * y := rfl

theorem coe_ennRat_ofRat (r : ℚ) : ((ENNRat.ofRat r : ℚ≥0∞) : ERat) = max r 0 := by
  simp [ENNRat.ofRat, ENNRat.toERat, Rat.toNNRat]

-- Needed for coe_ennRat_pow proof
theorem coe_ennRat_mul' (x y : ℚ≥0∞) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    ((x * y : ℚ≥0∞) : ERat) = (x : ERat) * y := by
  lift x to ℚ≥0 using hx
  lift y to ℚ≥0 using hy
  rfl

-- Casting from Nat to ERat via ℚ
theorem coe_coe_eq_natCast (n : ℕ) : ((n : ℚ) : ERat) = n := rfl

-- Coercion from ENNRat to ERat preserves order
theorem coe_ennRat_ne_top_iff {x : ℚ≥0∞} : (x : ERat) ≠ ⊤ ↔ x ≠ ⊤ := by
  cases x with
  | top => simp only [coe_ennRat_top, ne_eq, not_true_eq_false]
  | coe x => exact ⟨fun _ => ENNRat.coe_ne_top, fun _ => coe_ne_top x⟩

@[simp, norm_cast]
theorem coe_ennRat_le_coe_ennRat_iff {x y : ℚ≥0∞} : (x : ERat) ≤ (y : ERat) ↔ x ≤ y := by
  cases x with
  | top =>
    cases y with
    | top => simp only [coe_ennRat_top, le_refl]
    | coe y =>
      -- ⊤ ≤ (↑y : ERat) ↔ ⊤ ≤ (↑y : ℚ≥0∞), both false since y is finite
      simp only [coe_ennRat_top, top_le_iff]
      exact ⟨fun h => (coe_ne_top y h).elim, fun h => (ENNRat.coe_ne_top h).elim⟩
  | coe x =>
    cases y with
    | top => simp only [coe_ennRat_top, le_top]
    | coe y =>
      -- x y : ℚ≥0, the coercion chain ℚ≥0 → ℚ≥0∞ → ERat factors through ℚ
      -- ↑(↑x : ℚ≥0∞) : ERat = (x : ℚ) : ERat
      constructor
      · intro h; exact ENNRat.coe_le_coe.mpr (NNRat.coe_le_coe.mp (ERat.coe_le_coe_iff.mp h))
      · intro h; exact ERat.coe_le_coe_iff.mpr (NNRat.coe_le_coe.mpr (ENNRat.coe_le_coe.mp h))

@[gcongr] protected theorem coe_ennRat_le_coe_ennRat {x y : ℚ≥0∞} (h : x ≤ y) :
    (x : ERat) ≤ (y : ERat) := coe_ennRat_le_coe_ennRat_iff.mpr h

/-! ### Absolute value -/

-- TODO: use `Rat.nnabs` for the case `(x : ℚ)`
/-- The absolute value from `ERat` to `ℚ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a Rat `x` to `|x|`. -/
protected def abs : ERat → ℚ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℚ) => ENNRat.ofRat |x|

@[simp] theorem abs_top : (⊤ : ERat).abs = ⊤ := rfl

@[simp] theorem abs_bot : (⊥ : ERat).abs = ⊤ := rfl

theorem abs_def (x : ℚ) : (x : ERat).abs = ENNRat.ofRat |x| := rfl

theorem abs_coe_lt_top (x : ℚ) : (x : ERat).abs < ⊤ :=
  ENNRat.ofRat_lt_top

@[simp]
theorem abs_eq_zero_iff {x : ERat} : x.abs = 0 ↔ x = 0 := by
  induction x
  · simp only [abs_bot, ENNRat.top_ne_zero, bot_ne_zero]
  · simp only [abs_def, coe_eq_zero, ENNRat.ofRat_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNRat.top_ne_zero, top_ne_zero]

@[simp]
theorem abs_zero : (0 : ERat).abs = 0 := by rw [abs_eq_zero_iff]

@[simp]
theorem coe_abs (x : ℚ) : ((x : ERat).abs : ERat) = (|x| : ℚ) := by
  rw [abs_def, ← Rat.coe_nnabs, ENNRat.ofRat_coe_nnRat]; rfl

@[simp]
protected theorem abs_neg : ∀ x : ERat, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]

@[simp]
theorem abs_mul (x y : ERat) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, ERat.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNRat.ofRat_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, abs_top, ENNRat.top_mul]
    rw [Ne, abs_eq_zero_iff, coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, ERat.abs_neg, ERat.abs_neg]

/-! ### Sign -/

open SignType (sign)

theorem sign_top : sign (⊤ : ERat) = 1 := rfl

theorem sign_bot : sign (⊥ : ERat) = -1 := rfl

@[simp]
theorem sign_coe (x : ℚ) : sign (x : ERat) = sign x := by
  simp only [sign, OrderHom.coe_mk, ERat.coe_pos, ERat.coe_neg']

@[simp, norm_cast]
theorem coe_coe_sign (x : SignType) : ((x : ℚ) : ERat) = x := by cases x <;> rfl

@[simp] theorem sign_neg : ∀ x : ERat, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℚ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

@[simp]
theorem sign_mul (x y : ERat) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, ERat.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, sign_top, one_mul, sign_pos (ERat.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]

@[simp] protected theorem sign_mul_abs : ∀ x : ERat, (sign x * x.abs : ERat) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : ℚ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]

@[simp] protected theorem abs_mul_sign (x : ERat) : (x.abs * sign x : ERat) = x := by
  rw [ERat.mul_comm, ERat.sign_mul_abs]

theorem sign_eq_and_abs_eq_iff_eq {x y : ERat} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem le_iff_sign {x y : ERat} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

instance : CommMonoidWithZero ERat :=
  { inferInstanceAs (MulZeroOneClass ERat) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := ERat.mul_comm }

instance : PosMulMono ERat := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, ERat.sign_mul, sign_pos x0, one_mul, ERat.abs_mul] at h ⊢
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_left' · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_left' · _)

instance : MulPosMono ERat := posMulMono_iff_mulPosMono.1 inferInstance

instance : PosMulReflectLT ERat := PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT ERat := MulPosMono.toMulPosReflectLT

lemma mul_le_mul_of_nonpos_right {a b c : ERat} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c, ← neg_le_neg_iff, ← neg_mul c b, ← neg_mul c a]
  rw [← neg_zero, ERat.le_neg] at hc
  gcongr

@[simp, norm_cast]
theorem coe_pow (x : ℚ) (n : ℕ) : (↑(x ^ n) : ERat) = (x : ERat) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℚ →* ERat) _ _

private lemma top_pow_pos_erat : ∀ n : ℕ, (0 : ERat) < ⊤ ^ n
  | 0 => by simp
  | n + 1 => by
    simp only [pow_succ]
    exact ERat.mul_pos (top_pow_pos_erat n) zero_lt_top

@[simp, norm_cast]
theorem coe_ennRat_pow (x : ℚ≥0∞) (n : ℕ) : (↑(x ^ n) : ERat) = (x : ERat) ^ n := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · -- x = ⊤
    induction n with
    | zero => simp [coe_ennRat_one]
    | succ n ih =>
      simp only [ENNRat.top_pow (Nat.succ_ne_zero n), coe_ennRat_top, pow_succ]
      exact ((mul_comm _ _).trans (top_mul_of_pos (top_pow_pos_erat n))).symm
  · -- x is finite
    lift x to ℚ≥0 using hx
    -- For x : ℚ≥0, prove by induction on n
    induction n with
    | zero => simp only [pow_zero, coe_ennRat_one]
    | succ n ih =>
      simp only [pow_succ]
      -- Goal: ↑((↑x : ℚ≥0∞) ^ n * ↑x) = (↑(↑x : ℚ≥0∞) : ERat) ^ n * ↑(↑x : ℚ≥0∞)
      have h1 : ((↑x : ℚ≥0∞) ^ n) ≠ ⊤ := ENNRat.coe_ne_top
      have h2 : (↑x : ℚ≥0∞) ≠ ⊤ := ENNRat.coe_ne_top
      calc (((↑x : ℚ≥0∞) ^ n * (↑x : ℚ≥0∞) : ℚ≥0∞) : ERat)
          = (((↑x : ℚ≥0∞) ^ n : ℚ≥0∞) : ERat) * ((↑x : ℚ≥0∞) : ERat) :=
            coe_ennRat_mul' _ _ h1 h2
        _ = ((↑x : ℚ≥0∞) : ERat) ^ n * ((↑x : ℚ≥0∞) : ERat) := by congr 1

lemma exists_nat_ge_mul {a : ERat} (ha : a ≠ ⊤) (n : ℕ) :
    ∃ m : ℕ, a * n ≤ m :=
  match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := ERat) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : ℚ) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← ERat.coe_mul, ERat.coe_le_coe_iff]

/-! ### Min and Max -/

lemma min_neg_neg (x y : ERat) : min (-x) (-y) = -max x y := by
  rcases le_total x y with (h | h) <;> simp_all

lemma max_neg_neg (x y : ERat) : max (-x) (-y) = -min x y := by
  rcases le_total x y with (h | h) <;> simp_all

/-! ### Inverse -/

/-- Multiplicative inverse of an `ERat`. We choose `0⁻¹ = 0` to guarantee several good properties,
for instance `(a * b)⁻¹ = a⁻¹ * b⁻¹`. -/
protected def inv : ERat → ERat
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℚ) => (x⁻¹ : ℚ)

instance : Inv (ERat) := ⟨ERat.inv⟩

noncomputable instance : DivInvMonoid ERat where inv := ERat.inv

@[simp]
lemma inv_bot : (⊥ : ERat)⁻¹ = 0 := rfl

@[simp]
lemma inv_top : (⊤ : ERat)⁻¹ = 0 := rfl

lemma coe_inv (x : ℚ) : (x⁻¹ : ℚ) = (x : ERat)⁻¹ := rfl

@[simp]
lemma inv_zero : (0 : ERat)⁻¹ = 0 := by
  change (0 : ℚ)⁻¹ = (0 : ERat)
  rw [GroupWithZero.inv_zero, coe_zero]

noncomputable instance : DivInvOneMonoid ERat where
  inv_one := by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

lemma inv_neg (a : ERat) : (-a)⁻¹ = -a⁻¹ := by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact ERat.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

lemma inv_inv {a : ERat} (h : a ≠ ⊥) (h' : a ≠ ⊤) : (a⁻¹)⁻¹ = a := by
  rw [← coe_toRat h' h, ← coe_inv a.toRat, ← coe_inv a.toRat⁻¹, _root_.inv_inv a.toRat]

lemma mul_inv (a b : ERat) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction a, b using ERat.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (ERat.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (ERat.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (ERat.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (ERat.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

/-! #### Inversion and Absolute Value -/

lemma sign_mul_inv_abs (a : ERat) : (sign a) * (a.abs : ERat)⁻¹ = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennRat_ofRat, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · rw [coe_zero, sign_zero, SignType.coe_zero, abs_zero, coe_ennRat_zero, inv_zero, mul_zero]
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennRat_ofRat, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos

lemma sign_mul_inv_abs' (a : ERat) : (sign a) * ((a.abs⁻¹ : ℚ≥0∞) : ERat) = a⁻¹ := by
  induction a with
  | bot | top  => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofRat_inv_of_pos (abs_pos_of_neg a_neg), coe_ennRat_ofRat,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofRat_inv_of_pos (abs_pos_of_pos a_pos), coe_ennRat_ofRat,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

/-! #### Inversion and Positivity -/

lemma bot_lt_inv (x : ERat) : ⊥ < x⁻¹ := by
  cases x with
  | bot => exact inv_bot ▸ bot_lt_zero
  | top => exact ERat.inv_top ▸ bot_lt_zero
  | coe x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)

lemma inv_lt_top (x : ERat) : x⁻¹ < ⊤ := by
  cases x with
  | bot => exact inv_bot ▸ zero_lt_top
  | top => exact ERat.inv_top ▸ zero_lt_top
  | coe x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)

lemma inv_nonneg_of_nonneg {a : ERat} (h : 0 ≤ a) : 0 ≤ a⁻¹ := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, ERat.coe_nonneg, inv_nonneg]; exact ERat.coe_nonneg.1 h

lemma inv_nonpos_of_nonpos {a : ERat} (h : a ≤ 0) : a⁻¹ ≤ 0 := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, ERat.coe_nonpos, inv_nonpos]; exact ERat.coe_nonpos.1 h

lemma inv_pos_of_pos_ne_top {a : ERat} (h : 0 < a) (h' : a ≠ ⊤) : 0 < a⁻¹ := by
  lift a to ℚ using ⟨h', ne_bot_of_gt h⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h

lemma inv_neg_of_neg_ne_bot {a : ERat} (h : a < 0) (h' : a ≠ ⊥) : a⁻¹ < 0 := by
  lift a to ℚ using ⟨ne_top_of_lt h, h'⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h

lemma inv_strictAntiOn : StrictAntiOn (fun (x : ERat) => x⁻¹) (Ioi 0) := by
  intro a a_0 b b_0 a_b
  simp only [mem_Ioi] at *
  lift a to ℚ using ⟨ne_top_of_lt a_b, ne_bot_of_gt a_0⟩
  match b with
  | ⊤ => exact inv_top ▸ inv_pos_of_pos_ne_top a_0 (coe_ne_top a)
  | ⊥ => exact (not_lt_bot b_0).rec
  | (b : ℚ) =>
    rw [← coe_inv a, ← coe_inv b, ERat.coe_lt_coe_iff]
    exact _root_.inv_strictAntiOn (ERat.coe_pos.1 a_0) (ERat.coe_pos.1 b_0)
      (ERat.coe_lt_coe_iff.1 a_b)

/-! ### Division -/

protected lemma div_eq_inv_mul (a b : ERat) : a / b = b⁻¹ * a := ERat.mul_comm a b⁻¹

lemma coe_div (a b : ℚ) : (a / b : ℚ) = (a : ERat) / (b : ERat) := rfl

theorem natCast_div_le (m n : ℕ) :
    (m / n : ℕ) ≤ (m : ERat) / (n : ERat) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_div,
    ERat.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]
lemma div_bot {a : ERat} : a / ⊥ = 0 := inv_bot ▸ mul_zero a

@[simp]
lemma div_top {a : ERat} : a / ⊤ = 0 := inv_top ▸ mul_zero a

@[simp]
lemma div_zero {a : ERat} : a / 0 = 0 := by
  change a * 0⁻¹ = 0
  rw [inv_zero, mul_zero a]

@[simp]
lemma zero_div {a : ERat} : 0 / a = 0 := zero_mul a⁻¹

lemma top_div_of_pos_ne_top {a : ERat} (h : 0 < a) (h' : a ≠ ⊤) : ⊤ / a = ⊤ :=
  top_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma top_div_of_neg_ne_bot {a : ERat} (h : a < 0) (h' : a ≠ ⊥) : ⊤ / a = ⊥ :=
  top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

lemma bot_div_of_pos_ne_top {a : ERat} (h : 0 < a) (h' : a ≠ ⊤) : ⊥ / a = ⊥ :=
  bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma bot_div_of_neg_ne_bot {a : ERat} (h : a < 0) (h' : a ≠ ⊥) : ⊥ / a = ⊤ :=
  bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

/-! #### Division and Multiplication -/

lemma div_self {a : ERat} (h₁ : a ≠ ⊥) (h₂ : a ≠ ⊤) (h₃ : a ≠ 0) : a / a = 1 := by
  rw [← coe_toRat h₂ h₁] at h₃ ⊢
  rw [← coe_div, _root_.div_self (coe_ne_zero.1 h₃), coe_one]

lemma mul_div (a b c : ERat) : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

lemma mul_div_right (a b c : ERat) : a / b * c = a * c / b := by
  rw [mul_comm, ERat.mul_div, mul_comm]

lemma mul_div_left_comm (a b c : ERat) : a * (b / c) = b * (a / c) := by
  rw [mul_div a b c, mul_comm a b, ← mul_div b a c]

lemma div_div (a b c : ERat) : a / b / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹, mul_inv]

lemma div_mul_div_comm (a b c d : ERat) : a / b * (c / d) = a * c / (b * d) := by
  rw [← mul_div a, mul_comm b d, ← div_div c, ← mul_div_left_comm (c / d), mul_comm (a / b)]

variable {a b c : ERat}

lemma div_mul_cancel (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : a / b * b = a := by
  rw [mul_comm (a / b) b, ← mul_div_left_comm a b b, div_self h₁ h₂ h₃, mul_one]

lemma mul_div_cancel (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel h₁ h₂ h₃]

lemma mul_div_mul_cancel (h₁ : c ≠ ⊥) (h₂ : c ≠ ⊤) (h₃ : c ≠ 0) : a * c / (b * c) = a / b := by
  rw [← mul_div_right a (b * c) c, ← div_div a b c, div_mul_cancel h₁ h₂ h₃]

lemma div_eq_iff (hbot : b ≠ ⊥) (htop : b ≠ ⊤) (hzero : b ≠ 0) : c / b = a ↔ c = a * b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← @mul_div_cancel c b hbot htop hzero, h, mul_comm a b]
  · rw [h, mul_comm a b, ← mul_div b a b, @mul_div_cancel a b hbot htop hzero]

/-! #### Division and Order -/

lemma monotone_div_right_of_nonneg (h : 0 ≤ b) : Monotone fun a ↦ a / b :=
  fun _ _ h' ↦ mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

@[gcongr]
lemma div_le_div_right_of_nonneg (h : 0 ≤ c) (h' : a ≤ b) : a / c ≤ b / c :=
  monotone_div_right_of_nonneg h h'

lemma strictMono_div_right_of_pos (h : 0 < b) (h' : b ≠ ⊤) : StrictMono fun a ↦ a / b := by
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @ERat.mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h), hyp,
    @ERat.mul_div_cancel a' b (ne_bot_of_gt h) h' (ne_of_gt h)]

@[gcongr]
lemma div_lt_div_right_of_pos (h₁ : 0 < c) (h₂ : c ≠ ⊤) (h₃ : a < b) : a / c < b / c :=
  strictMono_div_right_of_pos h₁ h₂ h₃

lemma antitone_div_right_of_nonpos (h : b ≤ 0) : Antitone fun a ↦ a / b := by
  intro a a' h'
  change a' * b⁻¹ ≤ a * b⁻¹
  rw [← neg_neg (a * b⁻¹), ← neg_neg (a' * b⁻¹), neg_le_neg_iff, mul_comm a b⁻¹, mul_comm a' b⁻¹,
    ← neg_mul b⁻¹ a, ← neg_mul b⁻¹ a', mul_comm (-b⁻¹) a, mul_comm (-b⁻¹) a', ← inv_neg b]
  have : 0 ≤ -b := by apply ERat.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'

lemma div_le_div_right_of_nonpos (h : c ≤ 0) (h' : a ≤ b) : b / c ≤ a / c :=
  antitone_div_right_of_nonpos h h'

lemma strictAnti_div_right_of_neg (h : b < 0) (h' : b ≠ ⊥) : StrictAnti fun a ↦ a / b := by
  intro a a' a_lt_a'
  simp only
  apply lt_of_le_of_ne <| div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @ERat.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h), ← hyp,
    @ERat.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

lemma div_lt_div_right_of_neg (h₁ : c < 0) (h₂ : c ≠ ⊥) (h₃ : a < b) : b / c < a / c :=
  strictAnti_div_right_of_neg h₁ h₂ h₃

lemma le_div_iff_mul_le (h : b > 0) (h' : b ≠ ⊤) : a ≤ c / b ↔ a * b ≤ c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b a b, mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

lemma div_le_iff_le_mul (h : 0 < b) (h' : b ≠ ⊤) : a / b ≤ c ↔ a ≤ b * c := by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b c b, mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

lemma lt_div_iff (h : 0 < b) (h' : b ≠ ⊤) : a < c / b ↔ a * b < c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [ERat.mul_div b a b, mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

lemma div_lt_iff (h : 0 < c) (h' : c ≠ ⊤) :  b / c < a ↔ b < a * c := by
  nth_rw 1 [← @mul_div_cancel a c (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [ERat.mul_div c a c, mul_comm a c]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

lemma div_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg h (inv_nonneg_of_nonneg h')

lemma div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b ≠ ⊤) : 0 < a / b :=
  ERat.mul_pos ha (inv_pos_of_pos_ne_top hb hb')

lemma div_nonpos_of_nonpos_of_nonneg (h : a ≤ 0) (h' : 0 ≤ b) : a / b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

lemma div_nonpos_of_nonneg_of_nonpos (h : 0 ≤ a) (h' : b ≤ 0) : a / b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

lemma div_nonneg_of_nonpos_of_nonpos (h : a ≤ 0) (h' : b ≤ 0) : 0 ≤ a / b :=
  le_of_eq_of_le zero_div.symm (div_le_div_right_of_nonpos h' h)

private lemma exists_lt_mul_left_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Ioo 0 a, c < a' * b := by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩

private lemma exists_lt_mul_right_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Ioo 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

private lemma exists_mul_left_lt (h₁ : a ≠ 0 ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b) (hc : a * b < c) :
    ∃ a' ∈ Ioo a ⊤, a' * b < c := by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩

private lemma exists_mul_right_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ 0) (hc : a * b < c) :
    ∃ b' ∈ Ioo b ⊤, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc

lemma le_mul_of_forall_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b ≠ ⊤ := h₁.imp_left fun a0 ↦ a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' ≠ ⊤ ∨ b ≠ 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le

lemma mul_le_of_forall_lt_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ∈ Ioo 0 a, ∀ b' ∈ Ioo 0 b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d dab ↦ ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')

/-! #### Division Distributivity -/

-- TODO: These lemmas require right_distrib_of_nonneg which is commented out in ERat/Operations.lean
lemma div_right_distrib_of_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = a / c + b / c := by
  sorry

lemma add_div_of_nonneg_right (h : 0 ≤ c) :
    (a + b) / c = a / c + b / c := by
  sorry

end ERat

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: inverse of an `ERat`. -/
@[positivity (_⁻¹ : ERat)]
def evalERatInv : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ERat), ~q($a⁻¹) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa => pure (.nonnegative q(ERat.inv_nonneg_of_nonneg <| $pa))
    | none => pure .none
  | _, _, _ => throwError "not an inverse of an `ERat`"

/-- Extension for the `positivity` tactic: ratio of two `ERat`s. -/
@[positivity (_ / _ : ERat)]
def evalERatDiv : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ERat), ~q($a / $b) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(ERat.div_nonneg $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a ratio of 2 `ERat`s"

end Mathlib.Meta.Positivity
