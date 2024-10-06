import Init.Data.BitVec.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise

-- TODO: test how much these can be simplified using the SAT solver.

theorem Nat.testBit_lt_two_pow' {x : Nat} {i : Nat} : x < 2^i ↔ ∀ j, j ≥ i → Nat.testBit x j = false := by
  constructor
  · intro h
    intro j hj
    apply Nat.testBit_eq_false_of_lt
    apply lt_of_lt_of_le
    exact h
    apply pow_le_pow_right
    norm_num
    exact hj
  · intro h
    exact Nat.lt_pow_two_of_testBit x h

-- These two are from mathlib, but I don't think they're in the current version that I'm using
@[simp] theorem Nat.one_mod_two_pow_eq_one : 1 % 2 ^ n = 1 ↔ 0 < n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.mod_eq_of_lt (a := 1) (Nat.one_lt_two_pow (by omega))]
    simp

@[simp] theorem Nat.one_mod_two_pow (h : 0 < n) : 1 % 2 ^ n = 1 :=
  one_mod_two_pow_eq_one.mpr h


namespace BitVec

@[simp]
theorem allOnes_ne_zero {n : Nat} (h : n ≠ 0): BitVec.allOnes n ≠ 0 := by
  have := Nat.one_lt_two_pow_iff.mpr h
  intro ha
  apply (by omega :2^n - 1 ≠ 0)
  exact (BitVec.toNat_eq (BitVec.allOnes n) 0).mp ha

@[aesop safe]
theorem zero_ne_allOnes {n : Nat} (h : n ≠ 0) : 0 ≠ BitVec.allOnes n := by
  symm
  apply allOnes_ne_zero
  exact h

theorem one_or (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  if h : x = 0#1 then
    apply Or.intro_left
    exact h
  else
    apply Or.intro_right
    apply BitVec.eq_of_toNat_eq
    have i := x.isLt
    have h := (BitVec.toNat_ne _ _).mp h
    rw [pow_one] at i
    rw [toNat_ofNat, Nat.zero_mod, Nat.mod_succ] at *
    omega

theorem extractLsb'_cast {n m : Nat} (h : n = m) (start : Nat) (len : Nat) (x : BitVec n) : (BitVec.extractLsb' start len (x.cast h)) = BitVec.extractLsb' start len x := by
  unfold BitVec.cast BitVec.extractLsb'
  simp only [toNat_ofNatLt]

theorem func_cast_eq {n m : Nat} (h : n = m) (f : (l : Nat) → BitVec l → α) (x : BitVec n) : f m (x.cast h) = f n x := by
  cases h
  rfl

theorem cast_eq_swap {n m : Nat} (h : n = m) (x : BitVec n) (y : BitVec m) : x = (y.cast h.symm) ↔ x.cast h = y := by
  subst h
  simp_all only [cast_eq]

/-- If it is not equal to all ones, then it is less than all ones -/
theorem ne_allOnes_lt { n : Nat} (E : BitVec n) (hE : E ≠ BitVec.allOnes n) :
  E.toNat < 2 ^ n - 1 := by
  have hLt := E.isLt
  have hA : (BitVec.allOnes n).toNat = 2 ^ n - 1 := BitVec.toNat_allOnes
  have h : E.toNat ≠ (BitVec.allOnes n).toNat := (BitVec.toNat_ne _ _).mp hE
  omega

theorem ofNat_allOnes_eq_allOnes {n : Nat} : BitVec.ofNat n (2^n - 1) = BitVec.allOnes n := by
  unfold BitVec.allOnes
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, BitVec.toNat_ofNatLt]
  have nz : 2 ^ n ≠ 0 := by
    intro h
    have := (Nat.pow_eq_zero.mp h).left
    contradiction
  have : ∀ (a : ℕ), a ≠ 0 → a - 1 < a := by omega
  apply this _ nz

-- Has to use cast, which I wish we could replace with a better mechanism, since I don't really think the information about the sizes being equivalent should be in the proposition statement itself.
/-! BitVec.append is associative -/
theorem append_assoc {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b) ++ c = (a ++ (b ++ c)).cast (add_assoc n m r).symm := by
  ext
  rw [getLsb_append, getLsb_cast, getLsb_append, getLsb_append, getLsb_append]
  rename_i i

  if h1 : i < r then
    simp only [h1, decide_True, cond_true]
    if h2 : i < m + r then
      simp only [h2, decide_True, cond_true]
    else
      omega
  else
    simp only [h1, decide_False, cond_false]
    if h2 : i < m + r then
      simp only [h2, decide_True, cond_true]
      if h3 : i - r < m then
        simp only [h3, decide_True, cond_true]
      else
        omega
    else
      simp only [h2, decide_False, cond_false]
      if h3 : i - r < m then
        omega
      else
        simp only [h3, decide_False, cond_false]
        rw [Nat.add_comm m r, Nat.sub_add_eq]



/-- Extracting from the start of two concatenated bitvectors for the size of the start will result in the starting bitvector-/
theorem extractAppend_first₂ {n m : Nat} {a : BitVec n} {b : BitVec m} : (a ++ b).extractLsb' 0 m = b := by
  apply BitVec.eq_of_toNat_eq
  unfold extractLsb'
  rw [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.toNat_eq_nat, BitVec.ofNat_toNat]
  constructor
  exact BitVec.isLt b
  simp only [truncate_append, Nat.le_refl, ↓reduceDIte, zeroExtend_eq]

/-- Extracting from the end of two concatenated bitvectors for the size of the end will result in the ending bitvector-/
theorem extractAppend_second₂ {n m : Nat} {a : BitVec n} {b : BitVec m} : (a ++ b).extractLsb' m n = a := by
  apply BitVec.eq_of_toNat_eq
  unfold extractLsb'
  rw [toNat_append]
  apply Nat.eq_of_testBit_eq
  intro i
  unfold BitVec.toNat
  simp only [val_toFin, toFin_ofNat, Fin.val_ofNat', Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le,
    le_add_iff_nonneg_right, zero_le, decide_True, add_tsub_cancel_left, Bool.true_and]
  if h : i < n then
    simp_arith [h]
    intro h'
    let hb := b.isLt
    have j := Nat.testBit_lt_two_pow'.mp hb (m + i) (by omega)
    exfalso
    simp_all only [Bool.false_eq_true]
  else
    let ha := a.isLt
    simp only [h, decide_False, Bool.false_and, Bool.false_eq]
    exact Nat.testBit_lt_two_pow'.mp ha i (not_lt.mp h)

theorem extractAppend_first₃ {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b ++ c).extractLsb' 0 r = c := by
  apply extractAppend_first₂

theorem extractAppend_firstPart₃ {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b ++ c).extractLsb' 0 (m + r) = b ++ c := by
  rw [append_assoc]
  apply @extractAppend_first₂

theorem extractAppend_second₃ {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b ++ c).extractLsb' r m = b := by
  have k' := @extractAppend_first₂ n m a b
  conv =>
    rhs
    rw [← k']

  unfold extractLsb'
  rw [append_def, append_def]
  unfold BitVec.ofNat Fin.ofNat'
  norm_num
  congr
  unfold zeroExtend' BitVec.shiftLeftZeroExtend
  rw [toNat_ofNatLt, toNat_or, toNat_ofNatLt, toNat_ofNatLt]
  apply Nat.eq_of_testBit_eq
  intro i
  simp_arith
  intro h
  exfalso

  have j := Nat.testBit_lt_two_pow'.mp c.isLt (r + i) (by omega)
  simp_all only [Bool.false_eq_true]

theorem extractAppend_secondPart₃ {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b ++ c).extractLsb' r (n + m) = a ++ b := by
  apply @extractAppend_second₂

theorem extractAppend_third₃ {n m r : Nat} {a : BitVec n} {b : BitVec m} {c : BitVec r} : (a ++ b ++ c).extractLsb' (r + m) n = a := by
  have k'' := @extractAppend_second₂ n m a b
  conv =>
    rhs
    rw [← k'']

  unfold extractLsb'
  rw [append_def, append_def]
  unfold BitVec.ofNat Fin.ofNat'
  rw [toNat_or, toNat_zeroExtend', toNat_or, toNat_zeroExtend']
  norm_num

  unfold zeroExtend' BitVec.shiftLeftZeroExtend
  rw [toNat_ofNatLt, toNat_or, toNat_ofNatLt, toNat_ofNatLt]
  apply Nat.eq_of_testBit_eq
  intro i

  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    ge_iff_le, le_add_iff_nonneg_right, zero_le, decide_True, add_tsub_cancel_left, Bool.true_and]
  -- simp_arith


  if h1 : i < n then
    have a1 : r ≤ r + m + i := by omega
    have j := Nat.testBit_lt_two_pow'.mp b.isLt (m + i) (by norm_num)
    have j' := Nat.testBit_lt_two_pow'.mp c.isLt (r + m + i) (by omega)
    have a3 : r + m + i - r = m + i := by omega
    simp only [h1, decide_True, a1, a3, le_add_iff_nonneg_right, zero_le, add_tsub_cancel_left,
      Bool.true_and, j, Bool.or_false, j']
  else
    simp [h1, decide_False, Bool.false_and]

/-! Splitting into two bitvectors and concatenating them will result in the original bitvector -/
theorem extractBreakup₂ {n m : Nat} {s : BitVec (m + n)} : s.extractLsb' n m ++ s.extractLsb' 0 n = s := by
  apply BitVec.eq_of_toNat_eq
  unfold extractLsb'
  apply Nat.eq_of_testBit_eq

  intro i
  simp only [Nat.shiftRight_zero, ofNat_toNat, toNat_append, toNat_ofNat, toNat_truncate,
    Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]

  if h1 : i < n then
    simp only [h1, decide_True, Bool.true_and, Bool.or_iff_right_iff_imp, Bool.and_eq_true,
      decide_eq_true_eq, and_imp, isEmpty_Prop, not_le, IsEmpty.forall_iff]
  else
    have h1 : n ≤ i := by omega
    have h2 : ¬i < n := by omega
    simp_arith [h1, h2]
    intro a
    have k := s.isLt
    if h2 : i < n + m then
      omega
    else
      have j := Nat.testBit_lt_two_pow'.mp k i (by omega)
      simp_all only [Bool.false_eq_true]

theorem extractBreakup₃ {n m r : Nat} {s : BitVec (n + m + r)} : s.extractLsb' (m + r) n ++ s.extractLsb' r m ++ s.extractLsb' 0 r = s := by
  apply BitVec.eq_of_toNat_eq
  unfold extractLsb'
  apply Nat.eq_of_testBit_eq

  intro i
  simp only [Nat.shiftRight_zero, ofNat_toNat, toNat_append, toNat_ofNat, toNat_truncate,
    Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]

  if h1 : i < r then
    simp only [h1, decide_True, Bool.true_and, Bool.or_iff_right_iff_imp, Bool.and_eq_true,
      decide_eq_true_eq, Bool.or_eq_true, and_imp, isEmpty_Prop, not_le, IsEmpty.forall_iff]
  else
    simp_all only [not_lt, decide_True, add_tsub_cancel_of_le, Bool.true_and]
    if h2 : i = r then
      simp only [h2, le_refl, tsub_eq_zero_of_le, nonpos_iff_eq_zero, zero_le, add_zero,
        lt_self_iff_false, decide_False, Bool.false_and, Bool.or_false]
      if h3 : m = 0 then
        simp only [h3, decide_True, zero_add, Bool.true_and, lt_self_iff_false, decide_False,
          Bool.false_and, Bool.or_false, Bool.and_iff_right_iff_imp, decide_eq_true_eq]
        intro h
        if n = 0 then
          exfalso
          have j := Nat.testBit_lt_two_pow'.mp s.isLt i (by omega)
          simp_rw [← h2] at h
          simp_all only [le_refl, Bool.false_eq_true]
        else
          omega
      else
        simp_arith [h3]
        omega
    else
      if h3 : m ≤ i - r then
        simp only [h3, decide_True, Bool.true_and]
        if h4 : i - r < m then
          omega
        else
          have a3 : ¬i < r := by omega
          simp_arith [a3, h4]
          rw [show m + r + (i - r - m) = i by omega]
          if h5 : i - r - m < n then
            rw [Bool.and_iff_right_iff_imp, decide_eq_true_eq]
            omega
          else
            rw [Bool.and_iff_right_iff_imp, decide_eq_true_eq]
            contrapose!
            rw [Nat.testBit_lt_two_pow'.mp s.isLt i (by omega)]
            exact λ _ => Bool.false_ne_true
      else
        simp only [h3, decide_False, Bool.false_and, Bool.false_or]
        simp_all only [not_le, decide_True, Bool.true_and, Bool.or_iff_left_iff_imp,
          Bool.and_eq_true, decide_eq_true_eq, and_imp, implies_true]


end BitVec
