import Flean.Order

/-! # IEEE 754-2019 Min/Max Operations

IEEE 754-2019 §9.6 defines six min/max operations with different NaN semantics:

- `minimum` / `maximum`: propagate NaN (either NaN → result is NaN)
- `minimumNumber` / `maximumNumber`: ignore NaN (prefer the non-NaN operand)
- `minimumMagnitude` / `maximumMagnitude`: compare by absolute value, propagate NaN

All operations treat −0 < +0 per the total ordering.

Our `Fp` total order already has NaN < everything and −0 < +0, so we build on
the `LinearOrder Fp` infrastructure for the core comparison logic.
-/

namespace Fp

variable [FloatFormat]

/-! ## minimum / maximum (NaN-propagating) -/

/-- IEEE 754 `minimum`: returns NaN if either operand is NaN, otherwise the smaller value
    under total order (which treats −0 < +0). -/
def minimum (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | _, _ => if x ≤ y then x else y

/-- IEEE 754 `maximum`: returns NaN if either operand is NaN, otherwise the larger value
    under total order (which treats −0 < +0). -/
def maximum (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | _, _ => if y ≤ x then x else y

/-! ## minimumNumber / maximumNumber (NaN-ignoring) -/

/-- IEEE 754 `minimumNumber`: if exactly one operand is NaN, return the other.
    Both NaN → NaN. Otherwise the smaller value. -/
def minimumNumber (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ => y
  | _, .NaN => x
  | _, _ => if x ≤ y then x else y

/-- IEEE 754 `maximumNumber`: if exactly one operand is NaN, return the other.
    Both NaN → NaN. Otherwise the larger value. -/
def maximumNumber (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ => y
  | _, .NaN => x
  | _, _ => if y ≤ x then x else y

/-! ## minimumMagnitude / maximumMagnitude -/

/-- Absolute value on `Fp`: clears the sign bit. -/
def fpAbs (x : Fp) : Fp :=
  match x with
  | .finite f => .finite ⟨false, f.e, f.m, f.valid⟩
  | .infinite _ => .infinite false
  | .NaN => .NaN

/-- IEEE 754 `minimumMagnitude`: compare by absolute value, propagate NaN.
    On equal magnitude, prefer the value with smaller total order. -/
def minimumMagnitude (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | _, _ =>
    if fpAbs x < fpAbs y then x
    else if fpAbs y < fpAbs x then y
    else if x ≤ y then x else y

/-- IEEE 754 `maximumMagnitude`: compare by absolute value, propagate NaN.
    On equal magnitude, prefer the value with larger total order. -/
def maximumMagnitude (x y : Fp) : Fp :=
  match x, y with
  | .NaN, _ | _, .NaN => .NaN
  | _, _ =>
    if fpAbs y < fpAbs x then x
    else if fpAbs x < fpAbs y then y
    else if y ≤ x then x else y

/-! ## Basic properties -/

section NaN

@[simp] theorem minimum_nan_left (x : Fp) : minimum .NaN x = .NaN := by
  cases x <;> rfl

@[simp] theorem minimum_nan_right (x : Fp) : minimum x .NaN = .NaN := by
  cases x <;> rfl

@[simp] theorem maximum_nan_left (x : Fp) : maximum .NaN x = .NaN := by
  cases x <;> rfl

@[simp] theorem maximum_nan_right (x : Fp) : maximum x .NaN = .NaN := by
  cases x <;> rfl

@[simp] theorem minimumNumber_nan_left (x : Fp) : minimumNumber .NaN x = x := by
  cases x <;> rfl

@[simp] theorem minimumNumber_nan_right (x : Fp) : minimumNumber x .NaN = x := by
  cases x <;> rfl

@[simp] theorem maximumNumber_nan_left (x : Fp) : maximumNumber .NaN x = x := by
  cases x <;> rfl

@[simp] theorem maximumNumber_nan_right (x : Fp) : maximumNumber x .NaN = x := by
  cases x <;> rfl

@[simp] theorem minimumMagnitude_nan_left (x : Fp) : minimumMagnitude .NaN x = .NaN := by
  cases x <;> rfl

@[simp] theorem minimumMagnitude_nan_right (x : Fp) : minimumMagnitude x .NaN = .NaN := by
  cases x <;> rfl

@[simp] theorem maximumMagnitude_nan_left (x : Fp) : maximumMagnitude .NaN x = .NaN := by
  cases x <;> rfl

@[simp] theorem maximumMagnitude_nan_right (x : Fp) : maximumMagnitude x .NaN = .NaN := by
  cases x <;> rfl

end NaN

section NonNaN

/-- For non-NaN inputs, minimum/maximum pick one of the inputs. -/
private theorem not_nan_of_ite {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN)
    {p : Prop} [Decidable p] : ¬(if p then x else y).isNaN := by
  split <;> assumption

theorem minimum_not_nan {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    ¬(minimum x y).isNaN := by
  cases x with
  | NaN => exact absurd rfl hx
  | _ => cases y with
    | NaN => exact absurd rfl hy
    | _ => simp only [minimum]; exact not_nan_of_ite hx hy

theorem maximum_not_nan {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    ¬(maximum x y).isNaN := by
  cases x with
  | NaN => exact absurd rfl hx
  | _ => cases y with
    | NaN => exact absurd rfl hy
    | _ => simp only [maximum]; exact not_nan_of_ite hx hy

theorem minimumNumber_not_nan {x y : Fp} (hx : ¬x.isNaN) :
    ¬(minimumNumber x y).isNaN := by
  cases x with
  | NaN => exact absurd rfl hx
  | _ => cases y with
    | NaN => exact hx
    | _ => simp only [minimumNumber]; exact not_nan_of_ite hx (by simp [isNaN])

theorem maximumNumber_not_nan {x y : Fp} (hx : ¬x.isNaN) :
    ¬(maximumNumber x y).isNaN := by
  cases x with
  | NaN => exact absurd rfl hx
  | _ => cases y with
    | NaN => exact hx
    | _ => simp only [maximumNumber]; exact not_nan_of_ite hx (by simp [isNaN])

end NonNaN

section Bounds

theorem minimum_le_left {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    minimum x y ≤ x := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [minimum]; split
  all_goals first | exact le_refl _ | exact le_of_not_ge ‹_›

theorem minimum_le_right {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    minimum x y ≤ y := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [minimum]; split
  all_goals first | assumption | exact le_refl _

theorem le_maximum_left {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    x ≤ maximum x y := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [maximum]; split
  all_goals first | exact le_refl _ | exact le_of_not_ge ‹_›

theorem le_maximum_right {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    y ≤ maximum x y := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [maximum]; split
  all_goals first | assumption | exact le_refl _

theorem minimum_eq_or {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    minimum x y = x ∨ minimum x y = y := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [minimum]; split <;> simp

theorem maximum_eq_or {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    maximum x y = x ∨ maximum x y = y := by
  rcases x with f | b | _ <;> rcases y with g | c | _
  all_goals first | exact absurd rfl hx | exact absurd rfl hy | skip
  all_goals simp only [maximum]; split <;> simp

end Bounds

section Commutativity

/-- Helper: commutativity of `if x ≤ y then x else y`. -/
private theorem ite_le_comm (x y : Fp) :
    (if x ≤ y then x else y) = (if y ≤ x then y else x) := by
  rcases le_total x y with hxy | hxy <;> simp [hxy] <;> intro h <;>
    exact le_antisymm ‹_› ‹_›

/-- Helper: commutativity of `if y ≤ x then x else y`. -/
private theorem ite_ge_comm (x y : Fp) :
    (if y ≤ x then x else y) = (if x ≤ y then y else x) := by
  rcases le_total x y with hxy | hxy <;> simp [hxy] <;> intro h <;>
    exact le_antisymm ‹_› ‹_›

theorem minimum_comm (x y : Fp) : minimum x y = minimum y x := by
  cases x <;> cases y <;> simp [minimum, ite_le_comm]

theorem maximum_comm (x y : Fp) : maximum x y = maximum y x := by
  cases x <;> cases y <;> simp [maximum, ite_ge_comm]

theorem minimumNumber_comm (x y : Fp) : minimumNumber x y = minimumNumber y x := by
  cases x <;> cases y <;> simp [minimumNumber, ite_le_comm]

theorem maximumNumber_comm (x y : Fp) : maximumNumber x y = maximumNumber y x := by
  cases x <;> cases y <;> simp [maximumNumber, ite_ge_comm]

end Commutativity

section Idempotent

@[simp] theorem minimum_self (x : Fp) : minimum x x = x := by
  cases x <;> simp [minimum]

@[simp] theorem maximum_self (x : Fp) : maximum x x = x := by
  cases x <;> simp [maximum]

@[simp] theorem minimumNumber_self (x : Fp) : minimumNumber x x = x := by
  cases x <;> simp [minimumNumber]

@[simp] theorem maximumNumber_self (x : Fp) : maximumNumber x x = x := by
  cases x <;> simp [maximumNumber]

end Idempotent

section MinMaxRelation

theorem minimum_le_maximum {x y : Fp} (hx : ¬x.isNaN) (hy : ¬y.isNaN) :
    minimum x y ≤ maximum x y :=
  le_trans (minimum_le_left hx hy) (le_maximum_left hx hy)

end MinMaxRelation

end Fp
