import Flean.ENNRat.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Cast.CharZero


open Set NNRat ENNRat

namespace Rat

protected theorem _root_.Rat.toNNRat_mono : Monotone Rat.toNNRat := fun _ _ h =>
  max_le_max h (le_refl 0)

theorem toNNRat_le_toNNRat {r p : ℚ} (h : r ≤ p) : Rat.toNNRat r ≤ Rat.toNNRat p :=
  Rat.toNNRat_mono h

@[simp]
theorem toNNRat_eq_toNNRat_iff {r p : ℚ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    r.toNNRat = p.toNNRat ↔ r = p := by
    --simp [← NNRat.coe_inj, hr, hp]
    simp [toNNRat]

    -- rw [max_eq_left_iff.mpr hr]
    simp [max_eq_left hr, max_eq_left hp]
    grind

lemma toNNRat_le_toNNRat_iff' {r p : ℚ} : r.toNNRat ≤ p.toNNRat ↔ r ≤ p ∨ r ≤ 0 := by
  simp_rw [← not_lt, toNNRat_lt_toNNRat_iff', not_and_or]

@[simp]
lemma toNNRat_le_one {r : ℚ} : r.toNNRat ≤ 1 ↔ r ≤ 1 := by
  simpa using toNNRat_le_toNNRat_iff zero_le_one

@[simp]
lemma one_lt_toNNRat {r : ℚ} : 1 < r.toNNRat ↔ 1 < r := by
  simpa only [not_le] using toNNRat_le_one.not

@[simp]
lemma toNNRat_le_natCast {r : ℚ} {n : ℕ} : r.toNNRat ≤ n ↔ r ≤ n := by
  simpa using toNNRat_le_toNNRat_iff n.cast_nonneg

@[simp]
lemma natCast_lt_toNNRat {r : ℚ} {n : ℕ} : n < r.toNNRat ↔ n < r := by
  simpa only [not_le] using toNNRat_le_natCast.not

@[simp]
lemma ofNat_lt_toNNRat {r : ℚ} {n : ℕ} [n.AtLeastTwo] :
    ofNat(n) < r.toNNRat ↔ n < r :=
  natCast_lt_toNNRat

lemma toNNRat_eq_iff_eq_coe {r : ℚ} {p : ℚ≥0} (hp : p ≠ 0) : r.toNNRat = p ↔ r = p :=
  ⟨fun h ↦ h ▸ (coe_toNNRat _ <| not_lt.1 fun hlt ↦ hp <| h ▸ toNNRat_of_nonpos hlt.le).symm,
    fun h ↦ h.symm ▸ toNNRat_coe p⟩

@[simp]
lemma toNNRat_eq_one {r : ℚ} : r.toNNRat = 1 ↔ r = 1 := toNNRat_eq_iff_eq_coe one_ne_zero

@[simp]
lemma toNNRat_eq_natCast {r : ℚ} {n : ℕ} (hn : n ≠ 0) : r.toNNRat = n ↔ r = n :=
  mod_cast toNNRat_eq_iff_eq_coe <| Nat.cast_ne_zero.2 hn

@[simp]
lemma toNNRat_eq_ofNat {r : ℚ} {n : ℕ} [n.AtLeastTwo] :
    r.toNNRat = ofNat(n) ↔ r = OfNat.ofNat n :=
  toNNRat_eq_natCast (NeZero.ne n)

end Rat

namespace NNRat

theorem toNNRat_le_toNNRat {r p : ℚ} (h : r ≤ p) : Rat.toNNRat r ≤ Rat.toNNRat p :=
  Rat.toNNRat_mono h

end NNRat

namespace ENNRat

section Rat

variable {a b c d : ℚ≥0∞} {r p q : ℚ≥0}

theorem toRat_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toRat = a.toRat + b.toRat := by
  lift a to ℚ≥0 using ha
  lift b to ℚ≥0 using hb
  rfl

theorem toRat_add_le : (a + b).toRat ≤ a.toRat + b.toRat :=
  if ha : a = ∞ then by simp only [ha, top_add, toRat_top, zero_add, toRat_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toRat_top, add_zero, toRat_nonneg]
    else le_of_eq (toRat_add ha hb)

theorem ofRat_add {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNRat.ofRat (p + q) = ENNRat.ofRat p + ENNRat.ofRat q := by
  rw [ENNRat.ofRat, ENNRat.ofRat, ENNRat.ofRat, ← coe_add, coe_inj,
    Rat.toNNRat_add hp hq]

theorem ofRat_add_le {p q : ℚ} : ENNRat.ofRat (p + q) ≤ ENNRat.ofRat p + ENNRat.ofRat q :=
  coe_le_coe.2 Rat.toNNRat_add_le

@[simp]
theorem toRat_le_toRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toRat ≤ b.toRat ↔ a ≤ b := by
  lift a to ℚ≥0 using ha
  lift b to ℚ≥0 using hb
  simp only [ofNNRat_eq_NNRatCast, coe_toRat, cast_le, coe_le_coe]

@[gcongr]
theorem toRat_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toRat ≤ b.toRat :=
  (toRat_le_toRat (ne_top_of_le_ne_top hb h) hb).2 h

theorem toRat_mono' (h : a ≤ b) (ht : b = ∞ → a = ∞) : a.toRat ≤ b.toRat := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toRat_nonneg
  · exact toRat_mono (mt ht ha) h

@[simp]
theorem toRat_lt_toRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toRat < b.toRat ↔ a < b := by
  lift a to ℚ≥0 using ha
  lift b to ℚ≥0 using hb
  simp only [ofNNRat_eq_NNRatCast, coe_toRat, cast_lt, coe_lt_coe]

@[gcongr]
theorem toRat_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toRat < b.toRat :=
  (toRat_lt_toRat h.ne_top hb).2 h

@[gcongr]
theorem toNNRat_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNRat ≤ b.toNNRat :=
  toRat_mono hb h

theorem le_toNNRat_of_coe_le (h : p ≤ a) (ha : a ≠ ∞) : p ≤ a.toNNRat :=
  @toNNRat_coe p ▸ toNNRat_mono ha h

@[simp]
theorem toNNRat_le_toNNRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNRat ≤ b.toNNRat ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_toNNRat ha, ← coe_toNNRat hb, coe_le_coe], toNNRat_mono hb⟩

@[gcongr]
theorem toNNRat_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNRat < b.toNNRat := by
  simpa [← ENNRat.coe_lt_coe, hb, h.ne_top]

@[simp]
theorem toNNRat_lt_toNNRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNRat < b.toNNRat ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNRat ha, ← coe_toNNRat hb, coe_lt_coe], toNNRat_strict_mono hb⟩

theorem toNNRat_lt_of_lt_coe (h : a < p) : a.toNNRat < p :=
  @toNNRat_coe p ▸ toNNRat_strict_mono coe_ne_top h

theorem toRat_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNRat.toRat (max a b) = max (ENNRat.toRat a) (ENNRat.toRat b) :=
  (le_total a b).elim
    (fun h => by simp only [h, ENNRat.toRat_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNRat.toRat_mono hr h, max_eq_left]

theorem toRat_min {a b : ℚ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNRat.toRat (min a b) = min (ENNRat.toRat a) (ENNRat.toRat b) :=
  (le_total a b).elim (fun h => by simp only [h, ENNRat.toRat_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNRat.toRat_mono hr h, min_eq_right]

theorem toRat_sup {a b : ℚ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).toRat = a.toRat ⊔ b.toRat :=
  toRat_max

theorem toRat_inf {a b : ℚ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).toRat = a.toRat ⊓ b.toRat :=
  toRat_min

theorem toNNRat_pos_iff : 0 < a.toNNRat ↔ 0 < a ∧ a < ∞ := by
  induction a <;> simp

theorem toNNRat_pos {a : ℚ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNNRat :=
  toNNRat_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

theorem toRat_pos_iff : 0 < a.toRat ↔ 0 < a ∧ a < ∞ :=
  NNRat.coe_pos.trans toNNRat_pos_iff

theorem toRat_pos {a : ℚ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toRat :=
  toRat_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]
theorem ofRat_le_ofRat {p q : ℚ} (h : p ≤ q) : ENNRat.ofRat p ≤ ENNRat.ofRat q := by
  simp [ENNRat.ofRat, Rat.toNNRat_le_toNNRat h]

theorem ofRat_le_of_le_toRat {a : ℚ} {b : ℚ≥0∞} (h : a ≤ ENNRat.toRat b) :
    ENNRat.ofRat a ≤ b :=
  (ofRat_le_ofRat h).trans ofRat_toRat_le

@[simp]
theorem ofRat_le_ofRat_iff {p q : ℚ} (h : 0 ≤ q) :
    ENNRat.ofRat p ≤ ENNRat.ofRat q ↔ p ≤ q := by
  rw [ENNRat.ofRat, ENNRat.ofRat, coe_le_coe, Rat.toNNRat_le_toNNRat_iff h]

lemma ofRat_le_ofRat_iff' {p q : ℚ} : ENNRat.ofRat p ≤ .ofRat q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Rat.toNNRat_le_toNNRat_iff'

lemma ofRat_lt_ofRat_iff' {p q : ℚ} : ENNRat.ofRat p < .ofRat q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Rat.toNNRat_lt_toNNRat_iff'

@[simp]
theorem ofRat_eq_ofRat_iff {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNRat.ofRat p = ENNRat.ofRat q ↔ p = q := by
  rw [ENNRat.ofRat, ENNRat.ofRat, coe_inj, Rat.toNNRat_eq_toNNRat_iff hp hq]

@[simp]
theorem ofRat_lt_ofRat_iff {p q : ℚ} (h : 0 < q) :
    ENNRat.ofRat p < ENNRat.ofRat q ↔ p < q := by
  rw [ENNRat.ofRat, ENNRat.ofRat, coe_lt_coe, Rat.toNNRat_lt_toNNRat_iff h]

theorem ofRat_lt_ofRat_iff_of_nonneg {p q : ℚ} (hp : 0 ≤ p) :
    ENNRat.ofRat p < ENNRat.ofRat q ↔ p < q := by
  rw [ENNRat.ofRat, ENNRat.ofRat, coe_lt_coe, Rat.toNNRat_lt_toNNRat_iff_of_nonneg hp]

@[simp]
theorem ofRat_pos {p : ℚ} : 0 < ENNRat.ofRat p ↔ 0 < p := by simp [ENNRat.ofRat]

@[bound] private alias ⟨_, Bound.ofRat_pos_of_pos⟩ := ofRat_pos

@[simp]
theorem ofRat_eq_zero {p : ℚ} : ENNRat.ofRat p = 0 ↔ p ≤ 0 := by simp [ENNRat.ofRat]

theorem ofRat_ne_zero_iff {r : ℚ} : ENNRat.ofRat r ≠ 0 ↔ 0 < r := by
  rw [← zero_lt_iff, ENNRat.ofRat_pos]

@[simp]
theorem zero_eq_ofRat {p : ℚ} : 0 = ENNRat.ofRat p ↔ p ≤ 0 :=
  eq_comm.trans ofRat_eq_zero

alias ⟨_, ofRat_of_nonpos⟩ := ofRat_eq_zero

@[simp]
lemma ofRat_lt_natCast {p : ℚ} {n : ℕ} (hn : n ≠ 0) : ENNRat.ofRat p < n ↔ p < n := by
  exact mod_cast ofRat_lt_ofRat_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
lemma ofRat_lt_one {p : ℚ} : ENNRat.ofRat p < 1 ↔ p < 1 := by
  exact mod_cast ofRat_lt_natCast one_ne_zero

@[simp]
lemma ofRat_lt_ofNat {p : ℚ} {n : ℕ} [n.AtLeastTwo] :
    ENNRat.ofRat p < ofNat(n) ↔ p < OfNat.ofNat n :=
  ofRat_lt_natCast (NeZero.ne n)

@[simp]
lemma natCast_le_ofRat {n : ℕ} {p : ℚ} (hn : n ≠ 0) : n ≤ ENNRat.ofRat p ↔ n ≤ p := by
  simp only [← not_lt, ofRat_lt_natCast hn]

@[simp]
lemma one_le_ofRat {p : ℚ} : 1 ≤ ENNRat.ofRat p ↔ 1 ≤ p := by
  exact mod_cast natCast_le_ofRat one_ne_zero

@[simp]
lemma ofNat_le_ofRat {n : ℕ} [n.AtLeastTwo] {p : ℚ} :
    ofNat(n) ≤ ENNRat.ofRat p ↔ OfNat.ofNat n ≤ p :=
  natCast_le_ofRat (NeZero.ne n)

@[simp, norm_cast]
lemma ofRat_le_natCast {r : ℚ} {n : ℕ} : ENNRat.ofRat r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Rat.toNNRat_le_natCast

@[simp]
lemma ofRat_le_one {r : ℚ} : ENNRat.ofRat r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Rat.toNNRat_le_one

@[simp]
lemma ofRat_le_ofNat {r : ℚ} {n : ℕ} [n.AtLeastTwo] :
    ENNRat.ofRat r ≤ ofNat(n) ↔ r ≤ OfNat.ofNat n :=
  ofRat_le_natCast

@[simp]
lemma natCast_lt_ofRat {n : ℕ} {r : ℚ} : n < ENNRat.ofRat r ↔ n < r :=
  coe_lt_coe.trans Rat.natCast_lt_toNNRat

@[simp]
lemma one_lt_ofRat {r : ℚ} : 1 < ENNRat.ofRat r ↔ 1 < r := coe_lt_coe.trans Rat.one_lt_toNNRat

@[simp]
lemma ofNat_lt_ofRat {n : ℕ} [n.AtLeastTwo] {r : ℚ} :
    ofNat(n) < ENNRat.ofRat r ↔ OfNat.ofNat n < r :=
  natCast_lt_ofRat

@[simp]
lemma ofRat_eq_natCast {r : ℚ} {n : ℕ} (h : n ≠ 0) : ENNRat.ofRat r = n ↔ r = n :=
  ENNRat.coe_inj.trans <| Rat.toNNRat_eq_natCast h

@[simp]
lemma ofRat_eq_one {r : ℚ} : ENNRat.ofRat r = 1 ↔ r = 1 :=
  ENNRat.coe_inj.trans Rat.toNNRat_eq_one

@[simp]
lemma ofRat_eq_ofNat {r : ℚ} {n : ℕ} [n.AtLeastTwo] :
    ENNRat.ofRat r = ofNat(n) ↔ r = OfNat.ofNat n :=
  ofRat_eq_natCast (NeZero.ne n)

theorem ofRat_le_iff_le_toRat {a : ℚ} {b : ℚ≥0∞} (hb : b ≠ ∞) :
    ENNRat.ofRat a ≤ b ↔ a ≤ ENNRat.toRat b := by
  lift b to ℚ≥0 using hb
  simpa [ENNRat.ofNNRat_eq_NNRatCast, ENNRat.ofRat, ENNRat.toRat] using Rat.toNNRat_le_iff_le_coe

theorem ofRat_lt_iff_lt_toRat {a : ℚ} {b : ℚ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    ENNRat.ofRat a < b ↔ a < ENNRat.toRat b := by
  lift b to ℚ≥0 using hb
  simpa [ENNRat.ofNNRat_eq_NNRatCast, ENNRat.ofRat, ENNRat.toRat] using Rat.toNNRat_lt_iff_lt_coe ha

theorem ofRat_lt_coe_iff {a : ℚ} {b : ℚ≥0} (ha : 0 ≤ a) : ENNRat.ofRat a < b ↔ a < b :=
  (ofRat_lt_iff_lt_toRat ha coe_ne_top).trans <| by rw [coe_toRat]

theorem le_ofRat_iff_toRat_le {a : ℚ≥0∞} {b : ℚ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ ENNRat.ofRat b ↔ ENNRat.toRat a ≤ b := by
  lift a to ℚ≥0 using ha
  simpa [ENNRat.ofNNRat_eq_NNRatCast, ENNRat.ofRat, ENNRat.toRat] using Rat.le_toNNRat_iff_coe_le hb

theorem toRat_le_of_le_ofRat {a : ℚ≥0∞} {b : ℚ} (hb : 0 ≤ b) (h : a ≤ ENNRat.ofRat b) :
    ENNRat.toRat a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ofRat_ne_top h
  (le_ofRat_iff_toRat_le ha hb).1 h

theorem lt_ofRat_iff_toRat_lt {a : ℚ≥0∞} {b : ℚ} (ha : a ≠ ∞) :
    a < ENNRat.ofRat b ↔ ENNRat.toRat a < b := by
  lift a to ℚ≥0 using ha
  simpa [ENNRat.ofNNRat_eq_NNRatCast, ENNRat.ofRat, ENNRat.toRat] using Rat.lt_toNNRat_iff_coe_lt

theorem toRat_lt_of_lt_ofRat {b : ℚ} (h : a < ENNRat.ofRat b) : ENNRat.toRat a < b :=
  (lt_ofRat_iff_toRat_lt h.ne_top).1 h

theorem ofRat_mul {p q : ℚ} (hp : 0 ≤ p) :
    ENNRat.ofRat (p * q) = ENNRat.ofRat p * ENNRat.ofRat q := by
  simp only [ENNRat.ofRat, ← coe_mul, Rat.toNNRat_mul hp]

theorem ofRat_mul' {p q : ℚ} (hq : 0 ≤ q) :
    ENNRat.ofRat (p * q) = ENNRat.ofRat p * ENNRat.ofRat q := by
  rw [mul_comm, ofRat_mul hq, mul_comm]

theorem ofRat_pow {p : ℚ} (hp : 0 ≤ p) (n : ℕ) :
    ENNRat.ofRat (p ^ n) = ENNRat.ofRat p ^ n := by
  rw [ofRat_eq_coe_nnRat hp, ENNRat.ofNNRat_eq_NNRatCast, ← coe_pow, ← ofRat_coe_nnRat, NNRat.coe_pow, NNRat.coe_mk]

theorem ofRat_nsmul {x : ℚ} {n : ℕ} : ENNRat.ofRat (n • x) = n • ENNRat.ofRat x := by
  simp only [nsmul_eq_mul, ← ofRat_natCast n, ← ofRat_mul n.cast_nonneg]

@[simp]
theorem toNNRat_mul {a b : ℚ≥0∞} : (a * b).toNNRat = a.toNNRat * b.toNNRat :=
  WithTop.untopD_zero_mul a b

theorem toNNRat_mul_top (a : ℚ≥0∞) : ENNRat.toNNRat (a * ∞) = 0 := by simp

theorem toNNRat_top_mul (a : ℚ≥0∞) : ENNRat.toNNRat (∞ * a) = 0 := by simp

/-- `ENNRat.toNNRat` as a `MonoidHom`. -/
def toNNRatHom : ℚ≥0∞ →*₀ ℚ≥0 where
  toFun := ENNRat.toNNRat
  map_one' := toNNRat_coe _
  map_mul' _ _ := toNNRat_mul
  map_zero' := toNNRat_zero

@[simp]
theorem toNNRat_pow (a : ℚ≥0∞) (n : ℕ) : (a ^ n).toNNRat = a.toNNRat ^ n :=
  toNNRatHom.map_pow a n

/-- `ENNRat.toRat` as a `MonoidHom`. -/
def toRatHom : ℚ≥0∞ →*₀ ℚ :=
  (NNRat.castHom ℚ : ℚ≥0 →*₀ ℚ).comp toNNRatHom

@[simp]
theorem toRat_mul : (a * b).toRat = a.toRat * b.toRat :=
  toRatHom.map_mul a b

theorem toRat_nsmul (a : ℚ≥0∞) (n : ℕ) : (n • a).toRat = n • a.toRat := by simp

@[simp]
theorem toRat_pow (a : ℚ≥0∞) (n : ℕ) : (a ^ n).toRat = a.toRat ^ n :=
  toRatHom.map_pow a n

theorem toRat_ofRat_mul (c : ℚ) (a : ℚ≥0∞) (h : 0 ≤ c) :
    ENNRat.toRat (ENNRat.ofRat c * a) = c * ENNRat.toRat a := by
  rw [ENNRat.toRat_mul, ENNRat.toRat_ofRat h]

theorem toRat_mul_top (a : ℚ≥0∞) : ENNRat.toRat (a * ∞) = 0 := by
  rw [toRat_mul, toRat_top, mul_zero]

theorem toRat_top_mul (a : ℚ≥0∞) : ENNRat.toRat (∞ * a) = 0 := by
  rw [mul_comm]
  exact toRat_mul_top _

theorem toRat_eq_toRat (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toRat = b.toRat ↔ a = b := by
  lift a to ℚ≥0 using ha
  lift b to ℚ≥0 using hb
  simp [ENNRat.ofNNRat_eq_NNRatCast, coe_inj, NNRat.coe_inj, coe_toRat]

protected theorem trichotomy (p : ℚ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toRat := by
  simpa only [or_iff_not_imp_left] using toRat_pos

protected theorem trichotomy₂ {p q : ℚ≥0∞} (hpq : p ≤ q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toRat ∨
          p = ∞ ∧ q = ∞ ∨
            0 < p.toRat ∧ q = ∞ ∨ 0 < p.toRat ∧ 0 < q.toRat ∧ p.toRat ≤ q.toRat := by
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with (rfl | hq)
  · simpa using p.trichotomy
  repeat' right
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNRat.toRat_mono hq.ne hpq, ENNRat.toRat_pos_iff, hp, hp', hq', hq]

protected theorem dichotomy (p : ℚ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toRat :=
  haveI : p = ⊤ ∨ 0 < p.toRat ∧ 1 ≤ p.toRat := by
    simpa using ENNRat.trichotomy₂ (Fact.out : 1 ≤ p)
  this.imp_right fun h => h.2

theorem toRat_pos_iff_ne_top (p : ℚ≥0∞) [Fact (1 ≤ p)] : 0 < p.toRat ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    have : (0 : ℚ) ≠ 0 := toRat_top ▸ (hp ▸ h.ne : 0 ≠ ∞.toRat)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

end Rat

theorem sup_eq_zero {a b : ℚ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 :=
  sup_eq_bot_iff

end ENNRat

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNRat.ofRat`. -/
@[positivity ENNRat.ofRat _]
def evalENNRatOfRat : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℚ≥0∞), ~q(ENNRat.ofRat $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(Iff.mpr (@ENNRat.ofRat_pos $a) $pa))
    | _ => pure .none
  | _, _, _ => throwError "not ENNRat.ofRat"
end Mathlib.Meta.Positivity
