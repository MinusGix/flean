import Flean.Operations.KahanSum

/-!
# Pairwise Summation Error Bound

Extension C: pairwise (recursive) summation error bound `((1+η)^d - 1) · Σ|xᵢ|`
and comparison corollary showing Kahan beats pairwise for depth ≥ 3.
-/

namespace PairwiseSum

variable [FloatFormat]

/-- A pairwise summation trace: a binary tree of fp additions over a list. -/
inductive Trace [RModeExec] : List FiniteFp → FiniteFp → Type where
  | single (x : FiniteFp) : Trace [x] x
  | combine {xs ys : List FiniteFp} {a b : FiniteFp}
      (left : Trace xs a) (right : Trace ys b)
      (result : FiniteFp) (hadd : a + b = Fp.finite result) :
      Trace (xs ++ ys) result

/-- Depth of the computation tree. -/
def Trace.depth [RModeExec] :
    {xs : List FiniteFp} → {result : FiniteFp} → Trace xs result → ℕ
  | _, _, .single _ => 0
  | _, _, .combine left right _ _ => max left.depth right.depth + 1

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- Normal range at each node. -/
def Trace.AllNormalRange [RModeExec] :
    {xs : List FiniteFp} → {result : FiniteFp} → Trace xs result → Prop
  | _, _, .single _ => True
  | _, _, @Trace.combine _ _ _ _ a b left right _ _ =>
      left.AllNormalRange ∧ right.AllNormalRange ∧
      (isNormalRange ((a.toVal : R) + b.toVal) ∨ (a.toVal : R) + b.toVal = 0)

omit [FloatFormat] [FloorRing R] in
private lemma abs_sum_le_sum_abs (l : List R) :
    |l.sum| ≤ (l.map (fun x => |x|)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (abs_add_le x xs.sum) (add_le_add_right ih _)

omit [FloatFormat] [FloorRing R] in
private lemma abs_map_sum_le {α : Type*} (l : List α) (f : α → R) :
    |(l.map f).sum| ≤ (l.map (fun x => |f x|)).sum := by
  have h := abs_sum_le_sum_abs (l.map f)
  simp only [List.map_map] at h
  exact h

/-- **Pairwise summation error bound.**

    `|result - Σxᵢ| ≤ ((1+η)^d - 1) · Σ|xᵢ|` -/
theorem pairwise_error_bound
    [RModeExec] [RMode R] [RModeNearest R] [RoundIntSigMSound R]
    {xs : List FiniteFp} {result : FiniteFp}
    (trace : Trace xs result)
    (hnr : trace.AllNormalRange (R := R)) :
    |(result.toVal : R) - (xs.map (fun x => x.toVal (R := R))).sum| ≤
      ((1 + η) ^ trace.depth - 1) * (xs.map (fun x => |x.toVal (R := R)|)).sum := by
  induction trace with
  | single x => simp [Trace.depth]
  | @combine xs ys a b left right result hadd ih_left ih_right =>
    simp only [Trace.AllNormalRange] at hnr
    obtain ⟨hnr_left, hnr_right, hnr_add⟩ := hnr
    have hl := ih_left hnr_left
    have hr := ih_right hnr_right
    set dl := left.depth
    set dr := right.depth
    set Sl := (xs.map (fun x => |x.toVal (R := R)|)).sum
    set Sr := (ys.map (fun x => |x.toVal (R := R)|)).sum
    have hη : (0 : R) ≤ η := by positivity
    have hSl_nn : (0 : R) ≤ Sl := List.sum_nonneg (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨_, _, rfl⟩ := hy; exact abs_nonneg _)
    have hSr_nn : (0 : R) ≤ Sr := List.sum_nonneg (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨_, _, rfl⟩ := hy; exact abs_nonneg _)
    -- Addition error: |result - (a+b)| ≤ η|a+b| ≤ η(|a| + |b|)
    have hadd_err := KahanSum.fpAdd_error_or_zero (R := R) a b result hadd hnr_add
    have hab : |(a.toVal : R) + b.toVal| ≤ |a.toVal| + |b.toVal| := abs_add_le _ _
    -- Bound subtree results
    have ha_bound : |a.toVal (R := R)| ≤ (1 + η) ^ dl * Sl := by
      have h1 := abs_sub_abs_le_abs_sub (a.toVal (R := R))
        ((xs.map (fun x => x.toVal (R := R))).sum)
      have h2 : |(xs.map (fun x => x.toVal (R := R))).sum| ≤ Sl := abs_map_sum_le _ _
      nlinarith
    have hb_bound : |b.toVal (R := R)| ≤ (1 + η) ^ dr * Sr := by
      have h1 := abs_sub_abs_le_abs_sub (b.toVal (R := R))
        ((ys.map (fun x => x.toVal (R := R))).sum)
      have h2 : |(ys.map (fun x => x.toVal (R := R))).sum| ≤ Sr := abs_map_sum_le _ _
      nlinarith
    -- Combined add error bound
    have hadd_bound : |(result.toVal : R) - (a.toVal + b.toVal)| ≤
        (η : R) * (1 + η) ^ dl * Sl + η * (1 + η) ^ dr * Sr := by
      calc |(result.toVal : R) - (a.toVal + b.toVal)|
          ≤ η * |(a.toVal : R) + b.toVal| := hadd_err
        _ ≤ η * (|a.toVal| + |b.toVal|) := by nlinarith
        _ ≤ η * ((1 + η) ^ dl * Sl + (1 + η) ^ dr * Sr) := by nlinarith
        _ = η * (1 + η) ^ dl * Sl + η * (1 + η) ^ dr * Sr := by ring
    -- Sum and abs-sum splits
    have hval_split : ((xs ++ ys).map (fun x => x.toVal (R := R))).sum =
        (xs.map (fun x => x.toVal (R := R))).sum +
        (ys.map (fun x => x.toVal (R := R))).sum := by
      simp [List.map_append, List.sum_append]
    -- Triangle bound
    have htri : |(result.toVal : R) - ((xs ++ ys).map (fun x => x.toVal (R := R))).sum| ≤
        |(result.toVal : R) - (a.toVal + b.toVal)| +
        |a.toVal - (xs.map (fun x => x.toVal (R := R))).sum| +
        |b.toVal - (ys.map (fun x => x.toVal (R := R))).sum| := by
      have heq : (result.toVal : R) - ((xs ++ ys).map (fun x => x.toVal (R := R))).sum =
          (result.toVal - (a.toVal + b.toVal)) +
          (a.toVal - (xs.map (fun x => x.toVal (R := R))).sum) +
          (b.toVal - (ys.map (fun x => x.toVal (R := R))).sum) := by
        rw [hval_split]; ring
      rw [heq]
      have h1 := abs_add_le ((result.toVal : R) - (a.toVal + b.toVal))
        (a.toVal - (xs.map (fun x => x.toVal (R := R))).sum)
      have h2 := abs_add_le
        ((result.toVal : R) - (a.toVal + b.toVal) +
         (a.toVal - (xs.map (fun x => x.toVal (R := R))).sum))
        (b.toVal - (ys.map (fun x => x.toVal (R := R))).sum)
      linarith
    -- Rewrite append sums
    have habs_split : ((xs ++ ys).map (fun x => |x.toVal (R := R)|)).sum = Sl + Sr := by
      simp [Sl, Sr, List.map_append, List.sum_append]
    rw [hval_split] at htri
    -- Total bound before monotonicity
    have htotal : |(result.toVal : R) -
        ((xs.map (fun x => x.toVal (R := R))).sum +
         (ys.map (fun x => x.toVal (R := R))).sum)| ≤
        (η * (1 + η) ^ dl * Sl + ((1 + η) ^ dl - 1) * Sl) +
        (η * (1 + η) ^ dr * Sr + ((1 + η) ^ dr - 1) * Sr) := by
      linarith
    -- Algebraic step: η(1+η)^k · S + ((1+η)^k - 1)·S = ((1+η)^(k+1) - 1)·S
    have hstep_l : η * (1 + η) ^ dl * Sl + ((1 + η) ^ dl - 1) * Sl =
        ((1 + η) ^ (dl + 1) - 1) * Sl := by rw [pow_succ]; ring
    have hstep_r : η * (1 + η) ^ dr * Sr + ((1 + η) ^ dr - 1) * Sr =
        ((1 + η) ^ (dr + 1) - 1) * Sr := by rw [pow_succ]; ring
    -- Monotonicity
    have h1η : (1 : R) ≤ 1 + η := by linarith
    have hpow_dl : (1 + η : R) ^ (dl + 1) ≤ (1 + η) ^ (max dl dr + 1) :=
      pow_le_pow_right₀ h1η (by omega)
    have hpow_dr : (1 + η : R) ^ (dr + 1) ≤ (1 + η) ^ (max dl dr + 1) :=
      pow_le_pow_right₀ h1η (by omega)
    -- Multiply monotonicity by nonneg sums
    have hbound_l : ((1 + η : R) ^ (dl + 1) - 1) * Sl ≤
        ((1 + η) ^ (max dl dr + 1) - 1) * Sl := by nlinarith
    have hbound_r : ((1 + η : R) ^ (dr + 1) - 1) * Sr ≤
        ((1 + η) ^ (max dl dr + 1) - 1) * Sr := by nlinarith
    -- Chain to final bound
    have hfinal : |(result.toVal : R) -
        ((xs.map (fun x => x.toVal (R := R))).sum +
         (ys.map (fun x => x.toVal (R := R))).sum)| ≤
        ((1 + η) ^ (max dl dr + 1) - 1) * (Sl + Sr) :=
      calc |(result.toVal : R) - _|
          ≤ _ := htotal
        _ = ((1 + η) ^ (dl + 1) - 1) * Sl + ((1 + η) ^ (dr + 1) - 1) * Sr := by
            linarith [hstep_l, hstep_r]
        _ ≤ ((1 + η) ^ (max dl dr + 1) - 1) * Sl +
            ((1 + η) ^ (max dl dr + 1) - 1) * Sr := by
            linarith [hbound_l, hbound_r]
        _ = _ := by ring
    have hd_eq : Trace.depth (Trace.combine left right result hadd) = max dl dr + 1 := rfl
    rw [hd_eq, hval_split, habs_split]
    exact hfinal

/-! ## Comparison -/

omit [FloorRing R] in
/-- **Kahan beats pairwise for depth ≥ 3** (n ≥ 5 inputs).

    Under `nη < 1`: `2η + nη² < (1+η)^d - 1` for `d ≥ 3`. -/
theorem kahan_eps_lt_pairwise_eps (d : ℕ) (hd : 3 ≤ d) (n : ℕ)
    (hsmall : (n : R) * (η : R) < 1) :
    2 * (η : R) + (n : R) * (η : R) ^ 2 < ((1 + (η : R)) ^ d - 1) := by
  have hη : (0 : R) < η := by positivity
  have h1η : (1 : R) ≤ 1 + η := by linarith
  have hpow3 : (1 + (η : R)) ^ 3 ≥ 1 + 3 * η := by
    have : (1 + (η : R)) ^ 3 = 1 + 3 * η + 3 * η ^ 2 + η ^ 3 := by ring
    rw [this]; linarith [sq_nonneg (η : R), pow_nonneg (le_of_lt hη) 3]
  have hpow_d : (1 + (η : R)) ^ d ≥ (1 + η) ^ 3 := pow_le_pow_right₀ h1η hd
  nlinarith

end PairwiseSum
