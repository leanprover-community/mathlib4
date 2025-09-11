/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Weierstrass equations of elliptic curves

This file defines the structure of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map is
smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` for some `aᵢ`
in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`. If `R` is
a field, this quantity divides the discriminant of a cubic polynomial whose roots over a splitting
field of `R` are precisely the `X`-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

* `WeierstrassCurve`: a Weierstrass curve over a commutative ring.
* `WeierstrassCurve.Δ`: the discriminant of a Weierstrass curve.
* `WeierstrassCurve.map`: the Weierstrass curve mapped over a ring homomorphism.
* `WeierstrassCurve.twoTorsionPolynomial`: the 2-torsion polynomial of a Weierstrass curve.
* `WeierstrassCurve.IsElliptic`: typeclass asserting that a Weierstrass curve is an elliptic curve.
* `WeierstrassCurve.j`: the j-invariant of an elliptic curve.

## Main statements

* `WeierstrassCurve.twoTorsionPolynomial_disc`: the discriminant of a Weierstrass curve is a
  constant factor of the cubic discriminant of its 2-torsion polynomial.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum `Spec(R)` of `R` in the case that `R` has trivial Picard group
`Pic(R)` or, slightly more generally, when its 12-torsion is trivial. The issue is that for a
general ring `R`, there might be elliptic curves over `Spec(R)` in the sense of algebraic geometry
which are not globally defined by a cubic equation valid over the entire base.

## References

* [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
* [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

/-! ## Weierstrass curves -/

/-- A Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with parameters `aᵢ`. -/
@[ext]
structure WeierstrassCurve (R : Type u) where
  /-- The `a₁` coefficient of a Weierstrass curve. -/
  a₁ : R
  /-- The `a₂` coefficient of a Weierstrass curve. -/
  a₂ : R
  /-- The `a₃` coefficient of a Weierstrass curve. -/
  a₃ : R
  /-- The `a₄` coefficient of a Weierstrass curve. -/
  a₄ : R
  /-- The `a₆` coefficient of a Weierstrass curve. -/
  a₆ : R

namespace WeierstrassCurve

instance {R : Type u} [Inhabited R] : Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/

/-- The `b₂` coefficient of a Weierstrass curve. -/
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃

/-- The `b₆` coefficient of a Weierstrass curve. -/
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2

lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1

/-- The `c₄` coefficient of a Weierstrass curve. -/
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆

lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1

section CharTwo

variable [CharP R 2]

lemma b₂_of_char_two : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

lemma b₄_of_char_two : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

lemma b₆_of_char_two : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

lemma b₈_of_char_two :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 + W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

lemma c₄_of_char_two : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄, b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

lemma c₆_of_char_two : W.c₆ = W.a₁ ^ 6 := by
  rw [c₆, b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

lemma Δ_of_char_two : W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3 := by
  rw [Δ, b₂_of_char_two, b₄_of_char_two, b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

lemma b_relation_of_char_two : W.b₂ * W.b₆ = W.b₄ ^ 2 := by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

lemma c_relation_of_char_two : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

lemma b₂_of_char_three : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

lemma b₄_of_char_three : W.b₄ = -W.a₄ + W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

lemma b₆_of_char_three : W.b₆ = W.a₃ ^ 2 + W.a₆ := by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

lemma b₈_of_char_three :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

lemma c₄_of_char_three : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

lemma c₆_of_char_three : W.c₆ = -W.b₂ ^ 3 := by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

lemma Δ_of_char_three : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

lemma b_relation_of_char_three : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

lemma c_relation_of_char_three : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

end Quantity

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (f : R →+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩

variable (A) in
/-- The Weierstrass curve base changed to an algebra `A` over `R`. -/
abbrev baseChange [Algebra R A] : WeierstrassCurve A :=
  W.map <| algebraMap R A

@[simp]
lemma map_b₂ : (W.map f).b₂ = f W.b₂ := by
  simp only [b₂, map_a₁, map_a₂]
  map_simp

@[simp]
lemma map_b₄ : (W.map f).b₄ = f W.b₄ := by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp

@[simp]
lemma map_b₆ : (W.map f).b₆ = f W.b₆ := by
  simp only [b₆, map_a₃, map_a₆]
  map_simp

@[simp]
lemma map_b₈ : (W.map f).b₈ = f W.b₈ := by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp

@[simp]
lemma map_c₄ : (W.map f).c₄ = f W.c₄ := by
  simp only [c₄, map_b₂, map_b₄]
  map_simp

@[simp]
lemma map_c₆ : (W.map f).c₆ = f W.c₆ := by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp

@[simp]
lemma map_Δ : (W.map f).Δ = f W.Δ := by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

@[simp]
lemma map_id : W.map (RingHom.id R) = W :=
  rfl

lemma map_map {B : Type w} [CommRing B] (g : A →+* B) : (W.map f).map g = W.map (g.comp f) :=
  rfl

@[simp]
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (g : A →ₐ[S] B) : (W.baseChange A).map g = W.baseChange B :=
  congr_arg W.map <| g.comp_algebraMap_of_tower R

lemma map_injective {f : R →+* A} (hf : Function.Injective f) :
    Function.Injective <| map (f := f) := fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hf <;> assumption

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the `X`-coordinates of the non-zero 2-torsion points of `W`. -/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

lemma twoTorsionPolynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.disc]
  ring1

section CharTwo

variable [CharP R 2]

lemma twoTorsionPolynomial_of_char_two : W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

lemma twoTorsionPolynomial_disc_of_char_two : W.twoTorsionPolynomial.disc = 0 := by
  linear_combination W.twoTorsionPolynomial_disc + 8 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

lemma twoTorsionPolynomial_of_char_three : W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

lemma twoTorsionPolynomial_disc_of_char_three : W.twoTorsionPolynomial.disc = W.Δ := by
  linear_combination W.twoTorsionPolynomial_disc + 5 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
lemma twoTorsionPolynomial_disc_isUnit (hu : IsUnit (2 : R)) :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ := by
  rw [twoTorsionPolynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right <| hu.pow 4

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
-- TODO: In this case `IsUnit W.Δ` is just `W.IsElliptic`, consider removing/rephrasing this result
lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] (hu : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  ((W.twoTorsionPolynomial_disc_isUnit hu).mpr hΔ).ne_zero

end TorsionPolynomial

/-! ## Elliptic curves -/

-- TODO: change to `protected abbrev IsElliptic := IsUnit W.Δ` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- `WeierstrassCurve.IsElliptic` is a typeclass which asserts that a Weierstrass curve is an
elliptic curve: that its discriminant is a unit. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[mk_iff]
protected class IsElliptic : Prop where
  isUnit : IsUnit W.Δ

variable [W.IsElliptic]

lemma isUnit_Δ : IsUnit W.Δ := IsElliptic.isUnit

/-- The discriminant `Δ'` of an elliptic curve over `R`, which is given as a unit in `R`.
Note that to prove two equal elliptic curves have the same `Δ'`, you need to use `simp_rw`,
as `rw` cannot transfer instance `WeierstrassCurve.IsElliptic` automatically. -/
noncomputable def Δ' : Rˣ :=
  W.isUnit_Δ.unit

/-- The discriminant `Δ'` of an elliptic curve is equal to the
discriminant `Δ` of it as a Weierstrass curve. -/
@[simp]
lemma coe_Δ' : W.Δ' = W.Δ :=
  rfl

/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`.
Note that to prove two equal elliptic curves have the same `j`, you need to use `simp_rw`,
as `rw` cannot transfer instance `WeierstrassCurve.IsElliptic` automatically. -/
noncomputable def j : R :=
  W.Δ'⁻¹ * W.c₄ ^ 3

/-- A variant of `WeierstrassCurve.j_eq_zero_iff` without assuming a reduced ring. -/
lemma j_eq_zero_iff' : W.j = 0 ↔ W.c₄ ^ 3 = 0 := by
  rw [j, Units.mul_right_eq_zero]

lemma j_eq_zero (h : W.c₄ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff', h, zero_pow three_ne_zero]

lemma j_eq_zero_iff [IsReduced R] : W.j = 0 ↔ W.c₄ = 0 := by
  rw [j_eq_zero_iff', IsReduced.pow_eq_zero_iff three_ne_zero]

section CharTwo

variable [CharP R 2]

lemma j_of_char_two : W.j = W.Δ'⁻¹ * W.a₁ ^ 12 := by
  rw [j, W.c₄_of_char_two, ← pow_mul]

/-- A variant of `WeierstrassCurve.j_eq_zero_iff_of_char_two` without assuming a reduced ring. -/
lemma j_eq_zero_iff_of_char_two' : W.j = 0 ↔ W.a₁ ^ 12 = 0 := by
  rw [j_of_char_two, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_two (h : W.a₁ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_two', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_two [IsReduced R] : W.j = 0 ↔ W.a₁ = 0 := by
  rw [j_eq_zero_iff_of_char_two', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharTwo

section CharThree

variable [CharP R 3]

lemma j_of_char_three : W.j = W.Δ'⁻¹ * W.b₂ ^ 6 := by
  rw [j, W.c₄_of_char_three, ← pow_mul]

/-- A variant of `WeierstrassCurve.j_eq_zero_iff_of_char_three` without assuming a reduced ring. -/
lemma j_eq_zero_iff_of_char_three' : W.j = 0 ↔ W.b₂ ^ 6 = 0 := by
  rw [j_of_char_three, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_three (h : W.b₂ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_three', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_three [IsReduced R] : W.j = 0 ↔ W.b₂ = 0 := by
  rw [j_eq_zero_iff_of_char_three', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharThree

-- TODO: this is defeq to `twoTorsionPolynomial_disc_ne_zero` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged,
-- TODO: consider removing/rephrasing this result
lemma twoTorsionPolynomial_disc_ne_zero_of_isElliptic [Nontrivial R] (hu : IsUnit (2 : R)) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  W.twoTorsionPolynomial_disc_ne_zero hu W.isUnit_Δ

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (f : R →+* A)

instance : (W.map f).IsElliptic := by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]

set_option linter.docPrime false in
lemma coe_map_Δ' : (W.map f).Δ' = f W.Δ' := by
  rw [coe_Δ', map_Δ, coe_Δ']

set_option linter.docPrime false in
@[simp]
lemma map_Δ' : (W.map f).Δ' = Units.map f W.Δ' := by
  ext
  exact W.coe_map_Δ' f

set_option linter.docPrime false in
lemma coe_inv_map_Δ' : (W.map f).Δ'⁻¹ = f ↑W.Δ'⁻¹ := by
  simp

set_option linter.docPrime false in
lemma inv_map_Δ' : (W.map f).Δ'⁻¹ = Units.map f W.Δ'⁻¹ := by
  simp

@[simp]
lemma map_j : (W.map f).j = f W.j := by
  rw [j, coe_inv_map_Δ', map_c₄, j, map_mul, map_pow]

end BaseChange

end WeierstrassCurve
