import Flean.Operations.AffineFold
import Flean.Operations.Horner
import Flean.Operations.Clenshaw

/-!
# AffineFold Instances: Horner and Clenshaw

Shows that Horner (1D) and Clenshaw (2D) are instances of the generic `AffineFold`
framework, validating the abstraction.

For each algorithm:
1. The linear map `L` is additive
2. `affineFold L` equals the concrete evaluation function
3. `affineProp L` equals the concrete propagation function
4. The concrete affine theorem follows as a corollary
-/

namespace AffineFoldInstances

open AffineFold Horner Clenshaw

/-! ## Horner Instance -/

section Horner

variable {R : Type*} [Field R]

/-- Horner's linear map: `L(a) = x * a`. -/
def hornerL (x : R) : R → R := (x * ·)

theorem hornerL_additive (x : R) : ∀ a b : R, hornerL x (a + b) = hornerL x a + hornerL x b :=
  fun a b => by unfold hornerL; ring

/-- `affineFold` with `hornerL` equals `hornerPoly`. -/
theorem affineFold_eq_hornerPoly (cs : List R) (a x : R) :
    affineFold (hornerL x) cs a = hornerPoly cs a x := by
  induction cs generalizing a with
  | nil => simp [affineFold, hornerPoly]
  | cons c cs ih =>
    simp only [affineFold, hornerPoly, hornerL]
    rw [mul_comm x a]
    rw [ih]

/-- `affineProp` with `hornerL` equals `e * x^n`. -/
theorem affineProp_eq_horner (n : ℕ) (e x : R) :
    affineProp (hornerL x) n e = e * x ^ n := by
  induction n generalizing e with
  | zero => simp [affineProp]
  | succ n ih => simp only [affineProp, hornerL]; rw [ih]; ring

/-- `hornerPoly_affine` as a corollary of `affineFold_affine`. -/
theorem hornerPoly_affine_from_generic (cs : List R) (a e x : R) :
    hornerPoly cs (a + e) x = hornerPoly cs a x + e * x ^ cs.length := by
  rw [← affineFold_eq_hornerPoly, ← affineFold_eq_hornerPoly,
      ← affineProp_eq_horner]
  exact affineFold_affine (hornerL x) (hornerL_additive x) cs a e

end Horner

/-! ## Clenshaw Instance -/

section Clenshaw

variable {R : Type*} [Field R]

/-- Clenshaw's linear map: `L(a, b) = (w * a - b, a)`. -/
def clenshawL (w : R) : R × R → R × R := fun (a, b) => (w * a - b, a)

theorem clenshawL_additive (w : R) :
    ∀ a b, clenshawL w (a + b) = clenshawL w a + clenshawL w b :=
  fun (a₁, b₁) (a₂, b₂) => by
    simp only [clenshawL]
    simp [Prod.add_def, Prod.ext_iff]
    ring

/-- Convert a coefficient list to Clenshaw offsets `(c, 0)`. -/
def clenshawOffsets (cs : List R) : List (R × R) := cs.map (·, 0)

/-- `affineFold` with `clenshawL` and `clenshawOffsets` equals `clenshawExact`. -/
theorem affineFold_eq_clenshawExact (cs : List R) (a b w : R) :
    affineFold (clenshawL w) (clenshawOffsets cs) (a, b) = clenshawExact cs a b w := by
  induction cs generalizing a b with
  | nil => simp [affineFold, clenshawOffsets, clenshawExact]
  | cons c cs ih =>
    simp only [affineFold, clenshawOffsets, clenshawExact, clenshawL, List.map_cons]
    have : (w * a - b, a) + (c, (0 : R)) = (w * a - b + c, a) := by
      ext <;> simp [Prod.add_def]
    rw [this]
    exact ih _ _

/-- `affineProp` with `clenshawL` equals `clenshawProp`. -/
theorem affineProp_eq_clenshawProp (n : ℕ) (ea eb w : R) :
    affineProp (clenshawL w) n (ea, eb) = clenshawProp n ea eb w := by
  induction n generalizing ea eb with
  | zero => simp [affineProp, clenshawProp]
  | succ n ih => simp only [affineProp, clenshawProp, clenshawL]; exact ih _ _

/-- `clenshawExact_affine` as a corollary of `affineFold_affine`. -/
theorem clenshawExact_affine_from_generic (cs : List R) (a b ea eb w : R) :
    clenshawExact cs (a + ea) (b + eb) w =
      ((clenshawExact cs a b w).1 + (clenshawProp cs.length ea eb w).1,
       (clenshawExact cs a b w).2 + (clenshawProp cs.length ea eb w).2) := by
  have h := affineFold_affine (clenshawL w) (clenshawL_additive w)
    (clenshawOffsets cs) (a, b) (ea, eb)
  rw [affineFold_eq_clenshawExact, affineFold_eq_clenshawExact] at h
  have hlen : (clenshawOffsets cs).length = cs.length := by simp [clenshawOffsets]
  rw [hlen] at h
  rw [affineProp_eq_clenshawProp] at h
  simp only [Prod.add_def] at h
  have h1 := congr_arg Prod.fst h
  have h2 := congr_arg Prod.snd h
  simp only [] at h1 h2
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1, h2⟩

end Clenshaw

end AffineFoldInstances
