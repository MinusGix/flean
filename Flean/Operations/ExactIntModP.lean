import Flean.Operations.ExactIntAlgebra
import Mathlib.Data.ZMod.Basic

/-! # Structural shadows on `ExactInt`: ring-hom images of the exact integer

Every structure in the exact-int / reduction stack so far is a **value-fidelity** domain — it
answers "is this float an integer?" (`ExactInt`), "how far off a fixed-point value?"
(`ScaledInt`), "how big?" (`ExactIntB`). All metric. This file builds the first **structural**
family: discrete invariants of the exact integer a float represents — residues, parity, etc.

## The one abstraction: `IsImage`

The whole family rides on a fact `ExactInt` already proved — `.n` is a (partial) ring
homomorphism from the float computation to `ℤ`. Post-compose it with *any* ring hom out of `ℤ`
and the image still commutes with the ops, so the invariant propagates for free.

And there is exactly *one* ring hom out of `ℤ` for each target: `ℤ` is initial in `CommRing`, so
a structural shadow of this kind is determined entirely by **the choice of target commutative
ring `S`** (the hom is forced to be `Int.cast`). Hence a single generic predicate

  `IsImage (s : S) (a : ExactInt R) := (a.n : S) = s`

indexed only by `S`, with propagation proved **once**. The instances are then just choices of `S`:

* `S = ZMod p`            → residue mod `p`        (`IsResidue`)
* `S = ZMod p × ZMod q`   → CRT / simultaneous residues (`IsResiduePair`)
* `S = ℤ`                 → the exact value itself  (recovers `ExactInt` as the terminal-precision case)

Functoriality (`IsImage.map`) is what makes these a *category* rather than a list: a ring hom
`g : S →+* T` pushes a shadow forward (`IsImage s a → IsImage (g s) a`). So the *one* CRT fact in
`ZMod p × ZMod q` projects down to mod-`p` and mod-`q` separately via `RingHom.fst`/`snd` — one
computation, two structural shadows, from the shared machinery.

This is **idea-extraction**, not bounding: "this integer-valued float computation's shadow is a
fixed residue" is a *structural* statement about what the computation is, recovered from nothing
but the shadows of its inputs (the inputs' actual integers and float bit patterns stay abstract).

Design note: these discrete domains live on the **precise pillar** (`ExactInt`), not the
approximate one (`ScaledInt`). A residue is brittle — a ±1 shadow drift flips it — so it cannot
ride a growing `err`. The error story is the sub-½-ulp *snapping* bridge (recover the exact `n`
first, then take its image), which reduces to this exact case. See
`.claude/notes/exact-int-design.md`.
-/

namespace ExactInt

variable [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The generic structural shadow: the image of the represented integer `a.n` under the
canonical ring hom `ℤ → S` (unique, since `ℤ` is initial in `CommRing`) equals `s`. Every
ℤ-ring-hom-image domain is an instance, indexed only by the target commutative ring `S`. -/
def IsImage {S : Type*} [CommRing S] (s : S) (a : ExactInt R) : Prop := ((a.n : S) = s)

/-! ## Propagation through the total ops (no overflow conditions, no rounding typeclasses) -/

section Total
variable {S : Type*} [CommRing S]

@[simp] theorem isImage_zero : IsImage (R := R) (0 : S) (0 : ExactInt R) := by simp [IsImage]
@[simp] theorem isImage_one : IsImage (R := R) (1 : S) (1 : ExactInt R) := by simp [IsImage]

theorem IsImage.neg {s : S} {a : ExactInt R} (ha : IsImage s a) : IsImage (-s) (-a) := by
  show ((-a).n : S) = -s
  rw [neg_n, Int.cast_neg, ha]

/-- Functoriality: a ring hom `g : S →+* T` pushes a structural shadow forward. This is what
makes these domains a *category* — the CRT shadow in `ZMod p × ZMod q` projects to mod-`p` and
mod-`q` by `g = RingHom.fst`/`snd`. The proof is just that `g` commutes with `Int.cast`. -/
theorem IsImage.map {T : Type*} [CommRing T] (g : S →+* T) {s : S} {a : ExactInt R}
    (ha : IsImage s a) : IsImage (g s) a := by
  show ((a.n : T) = g s)
  rw [← ha, map_intCast]

end Total

/-! ## Instance 0: the exact value itself  (`S = ℤ`, identity hom)

`IsImage` at the target `ℤ` is the identity hom (`Int.cast : ℤ → ℤ`), so it recovers `ExactInt`'s
own integer — the **terminal-precision point** of the family, its top element. Every coarser
structural shadow factors through it: from the exact value you derive *any* image, by
`IsImage.map` along the canonical `ℤ →+* S`. This makes the "domains form a lattice with
`ExactInt` on top" claim literal. -/

/-- The exact-value shadow: `IsImage` at `S = ℤ`, i.e. the represented integer is exactly `n`. -/
def IsExactly (n : ℤ) (a : ExactInt R) : Prop := IsImage n a

/-- Unfolding: `IsExactly` is just `ExactInt`'s tracked integer (the `ℤ → ℤ` hom is identity). -/
theorem isExactly_iff {n : ℤ} {a : ExactInt R} : IsExactly n a ↔ a.n = n := by
  simp only [IsExactly, IsImage, Int.cast_id]

/-- Every `ExactInt` is exactly its own tracked integer — the canonical embedding into the
shadow family. -/
@[simp] theorem isExactly_self (a : ExactInt R) : IsExactly a.n a := by
  simp only [IsExactly, IsImage, Int.cast_id]

/-- The universal factoring: the exact value determines the image in *every* target ring. Coarser
shadows (`IsResidue p`, `IsResiduePair`, …) are all specializations at a choice of `S`. -/
theorem IsExactly.toImage {S : Type*} [CommRing S] {n : ℤ} {a : ExactInt R}
    (h : IsExactly n a) : IsImage (n : S) a :=
  IsImage.map (Int.castRingHom S) h

/-! ## Propagation through the partial ops (under a no-overflow bound)

These need the rounding typeclasses only because `ExactInt.add`/`mul`/`sub` are *defined* under
them — the image proof itself uses nothing beyond the `.n` ring-hom lemmas + `Int.cast_*`. -/

section Partial
variable {S : Type*} [CommRing S]
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

theorem IsImage.add {s_a s_b : S} {a b : ExactInt R}
    (ha : IsImage s_a a) (hb : IsImage s_b b)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsImage (s_a + s_b) (a.add b hbound h_exp) := by
  show ((a.add b hbound h_exp).n : S) = s_a + s_b
  rw [add_n, Int.cast_add, ha, hb]

theorem IsImage.sub {s_a s_b : S} {a b : ExactInt R}
    (ha : IsImage s_a a) (hb : IsImage s_b b)
    (hbound : (a.n - b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsImage (s_a - s_b) (a.sub b hbound h_exp) := by
  show ((a.sub b hbound h_exp).n : S) = s_a - s_b
  rw [sub_n, Int.cast_sub, ha, hb]

theorem IsImage.mul {s_a s_b : S} {a b : ExactInt R}
    (ha : IsImage s_a a) (hb : IsImage s_b b)
    (hbound : (a.n * b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsImage (s_a * s_b) (a.mul b hbound h_exp) := by
  show ((a.mul b hbound h_exp).n : S) = s_a * s_b
  rw [mul_n, Int.cast_mul, ha, hb]

/-- A length-2 integer dot product carries its shadow: given the shadows of the four inputs, the
shadow of the float result is pinned to `s_a₁·s_b₁ + s_a₂·s_b₂`, the inputs' integers and bit
patterns left abstract. -/
theorem IsImage.dot2 {a₁ b₁ a₂ b₂ : ExactInt R} {sa₁ sb₁ sa₂ sb₂ : S}
    (ha₁ : IsImage sa₁ a₁) (hb₁ : IsImage sb₁ b₁)
    (ha₂ : IsImage sa₂ a₂) (hb₂ : IsImage sb₂ b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsImage (sa₁ * sb₁ + sa₂ * sb₂) (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) := by
  show ((ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp).n : S) = sa₁ * sb₁ + sa₂ * sb₂
  rw [dot2_n, Int.cast_add, Int.cast_mul, Int.cast_mul, ha₁, hb₁, ha₂, hb₂]

end Partial

/-! ## Instance 1: residue mod `p`  (`S = ZMod p`)

mod-p is `IsImage` at `S = ZMod p`. The whole API is recovered by delegation — mod-p needs *no
propagation proof of its own*, which is precisely the "abstraction earns its keep" evidence. -/

/-- The integer an `ExactInt` represents has residue `r` mod `p`: `IsImage` at `S = ZMod p`. -/
def IsResidue (p : ℕ) (r : ZMod p) (a : ExactInt R) : Prop := IsImage r a

@[simp] theorem isResidue_zero (p : ℕ) : IsResidue (R := R) p 0 (0 : ExactInt R) := isImage_zero
@[simp] theorem isResidue_one (p : ℕ) : IsResidue (R := R) p 1 (1 : ExactInt R) := isImage_one

/-- The exact value determines the residue: knowing `a` represents `n` exactly fixes its
residue `(n : ZMod p)` mod every `p`. The `S = ZMod p` specialization of `IsExactly.toImage`. -/
theorem IsExactly.toResidue {n : ℤ} {a : ExactInt R} (p : ℕ)
    (h : IsExactly n a) : IsResidue p (n : ZMod p) a := h.toImage

theorem IsResidue.neg {p : ℕ} {r : ZMod p} {a : ExactInt R}
    (ha : IsResidue p r a) : IsResidue p (-r) (-a) := IsImage.neg ha

section ModPPartial
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

theorem IsResidue.add {p : ℕ} {r_a r_b : ZMod p} {a b : ExactInt R}
    (ha : IsResidue p r_a a) (hb : IsResidue p r_b b)
    (hbound : (a.n + b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue p (r_a + r_b) (a.add b hbound h_exp) := IsImage.add ha hb hbound h_exp

theorem IsResidue.sub {p : ℕ} {r_a r_b : ZMod p} {a b : ExactInt R}
    (ha : IsResidue p r_a a) (hb : IsResidue p r_b b)
    (hbound : (a.n - b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue p (r_a - r_b) (a.sub b hbound h_exp) := IsImage.sub ha hb hbound h_exp

theorem IsResidue.mul {p : ℕ} {r_a r_b : ZMod p} {a b : ExactInt R}
    (ha : IsResidue p r_a a) (hb : IsResidue p r_b b)
    (hbound : (a.n * b.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue p (r_a * r_b) (a.mul b hbound h_exp) := IsImage.mul ha hb hbound h_exp

theorem IsResidue.dot2 {p : ℕ} {a₁ b₁ a₂ b₂ : ExactInt R} {ra₁ rb₁ ra₂ rb₂ : ZMod p}
    (ha₁ : IsResidue p ra₁ a₁) (hb₁ : IsResidue p rb₁ b₁)
    (ha₂ : IsResidue p ra₂ a₂) (hb₂ : IsResidue p rb₂ b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue p (ra₁ * rb₁ + ra₂ * rb₂) (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) :=
  IsImage.dot2 ha₁ hb₁ ha₂ hb₂ h₁b h₂b hsb h_exp

/-- Extraction with a fixed modulus, fully concrete: from only the residues of the inputs
mod 7, the residue of the length-2 dot product is *determined* — `3·4 + 2·5 ≡ 1 (mod 7)`. The
actual integers the floats represent are irrelevant; the residue is a property of the
computation's structure, not its data. -/
theorem dot2_residue_mod7 {a₁ b₁ a₂ b₂ : ExactInt R}
    (ha₁ : IsResidue 7 3 a₁) (hb₁ : IsResidue 7 4 b₁)
    (ha₂ : IsResidue 7 2 a₂) (hb₂ : IsResidue 7 5 b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue 7 1 (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) := by
  have h := IsResidue.dot2 ha₁ hb₁ ha₂ hb₂ h₁b h₂b hsb h_exp
  have heval : ((3 : ZMod 7) * 4 + 2 * 5) = 1 := by decide
  rwa [heval] at h

end ModPPartial

/-! ## Instance 2: CRT / simultaneous residues  (`S = ZMod p × ZMod q`)

The second structural instance — a genuinely different target ring, to poke the `IsImage`
abstraction. It needs no propagation proofs either, and the *one* pair-shadow projects down to
each modulus via the functorial `IsImage.map`, with the projection ring homs `RingHom.fst`/`snd`.
That projection is content mod-p alone could not exhibit. -/

/-- Track residues mod `p` and mod `q` simultaneously, in the product ring `ZMod p × ZMod q`
(by CRT, equivalent to a residue mod `lcm p q` when `p`, `q` coprime). `IsImage` at the product
target. -/
def IsResiduePair (p q : ℕ) (r : ZMod p × ZMod q) (a : ExactInt R) : Prop := IsImage r a

/-- Projecting the CRT shadow onto the first modulus: the represented integer's mod-`p` residue
is the first component. Pure `IsImage.map` along `RingHom.fst`. -/
theorem IsResiduePair.fst {p q : ℕ} {r : ZMod p × ZMod q} {a : ExactInt R}
    (h : IsResiduePair p q r a) : IsResidue p r.1 a :=
  IsImage.map (RingHom.fst (ZMod p) (ZMod q)) h

/-- Projecting the CRT shadow onto the second modulus. Pure `IsImage.map` along `RingHom.snd`. -/
theorem IsResiduePair.snd {p q : ℕ} {r : ZMod p × ZMod q} {a : ExactInt R}
    (h : IsResiduePair p q r a) : IsResidue q r.2 a :=
  IsImage.map (RingHom.snd (ZMod p) (ZMod q)) h

section CRTPartial
variable [FloorRing R] [RMode R] [RModeExec] [RoundIntSigMSound R] [RModeIdem R]

theorem IsResiduePair.dot2 {p q : ℕ} {a₁ b₁ a₂ b₂ : ExactInt R}
    {ra₁ rb₁ ra₂ rb₂ : ZMod p × ZMod q}
    (ha₁ : IsResiduePair p q ra₁ a₁) (hb₁ : IsResiduePair p q rb₁ b₁)
    (ha₂ : IsResiduePair p q ra₂ a₂) (hb₂ : IsResiduePair p q rb₂ b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResiduePair p q (ra₁ * rb₁ + ra₂ * rb₂)
      (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) :=
  IsImage.dot2 ha₁ hb₁ ha₂ hb₂ h₁b h₂b hsb h_exp

/-- CRT headline: one integer dot product carries residues mod 3 AND mod 5 at once. Given the
pair-shadows of the inputs, the result is `≡ 1 (mod 3)` and `≡ 1 (mod 5)` simultaneously (hence
`≡ 1 mod 15`) — and *both* facts are projections of the single `IsResiduePair.dot2` result
through the functorial `IsImage.map`. The shared machinery does all the work. -/
theorem dot2_residue_crt_3_5 {a₁ b₁ a₂ b₂ : ExactInt R}
    (ha₁ : IsResiduePair 3 5 (2, 4) a₁) (hb₁ : IsResiduePair 3 5 (1, 2) b₁)
    (ha₂ : IsResiduePair 3 5 (2, 1) a₂) (hb₂ : IsResiduePair 3 5 (1, 3) b₂)
    (h₁b : (a₁.n * b₁.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h₂b : (a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (hsb : (a₁.n * b₁.n + a₂.n * b₂.n).natAbs < 2 ^ FloatFormat.prec.toNat)
    (h_exp : FloatFormat.prec - 1 ≤ FloatFormat.max_exp) :
    IsResidue 3 1 (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) ∧
    IsResidue 5 1 (ExactInt.dot2 a₁ b₁ a₂ b₂ h₁b h₂b hsb h_exp) := by
  have h := IsResiduePair.dot2 ha₁ hb₁ ha₂ hb₂ h₁b h₂b hsb h_exp
  have heval : (((2, 4) : ZMod 3 × ZMod 5) * (1, 2) + (2, 1) * (1, 3)) = (1, 1) := by decide
  rw [heval] at h
  exact ⟨h.fst, h.snd⟩

end CRTPartial

end ExactInt
