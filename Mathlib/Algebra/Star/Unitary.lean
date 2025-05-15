/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `Matrix.UnitaryGroup` for specializations to `unitary (Matrix n n R)`.

## Tags

unitary
-/


/-- In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_setOf_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]

variable {R : Type*}

namespace unitary

section Monoid

variable [Monoid R] [StarMul R]

theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl

@[simp]
theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 :=
  hU.1

@[simp]
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2

theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl

theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.prop

theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.prop

@[simp]
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
  Subtype.ext <| coe_star_mul_self U

@[simp]
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
  Subtype.ext <| coe_mul_star_self U

instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }

instance : InvolutiveStar (unitary R) :=
  ⟨by
    intro x
    ext
    rw [coe_star, coe_star, star_star]⟩

instance : StarMul (unitary R) :=
  ⟨by
    intro x y
    ext
    rw [coe_star, Submonoid.coe_mul, Submonoid.coe_mul, coe_star, coe_star, star_mul]⟩

instance : Inhabited (unitary R) :=
  ⟨1⟩

theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl

theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl

/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

theorem toUnits_injective : Function.Injective (toUnits : unitary R → Rˣ) := fun _ _ h =>
  Subtype.ext <| Units.ext_iff.mp h

theorem _root_.IsUnit.mem_unitary_iff_star_mul_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ star u * u = 1 := by
  rw [unitary.mem_iff, and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

theorem _root_.IsUnit.mem_unitary_iff_mul_star_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ u * star u = 1 := by
  rw [← star_mem_iff, hu.star.mem_unitary_iff_star_mul_self, star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self

lemma mul_inv_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a * b⁻¹ ∈ unitary G ↔ star a * a = star b * b := by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self, star_mul, star_inv, mul_assoc,
    inv_mul_eq_iff_eq_mul, mul_one, ← mul_assoc, mul_inv_eq_iff_eq_mul]

lemma inv_mul_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a⁻¹ * b ∈ unitary G ↔ a * star a = b * star b := by
  simpa [← mul_inv_rev] using mul_inv_mem_iff a⁻¹ b⁻¹

theorem _root_.Units.unitary_eq : unitary Rˣ = (unitary R).comap (Units.coeHom R) := by
  ext
  simp [unitary.mem_iff, Units.ext_iff]

/-- In a star monoid, the product `a * b⁻¹` of units is unitary if `star a * a = star b * b`. -/
protected lemma _root_.Units.mul_inv_mem_unitary (a b : Rˣ) :
    (a * b⁻¹ : R) ∈ unitary R ↔ star a * a = star b * b := by
  simp [← mul_inv_mem_iff, Units.unitary_eq]

/-- In a star monoid, the product `a⁻¹ * b` of units is unitary if `a * star a = b * star b`. -/
protected lemma _root_.Units.inv_mul_mem_unitary (a b : Rˣ) :
    (a⁻¹ * b : R) ∈ unitary R ↔ a * star a = b * star b := by
  simp [← inv_mul_mem_iff, Units.unitary_eq]

instance instIsStarNormal (u : unitary R) : IsStarNormal u where
  star_comm_self := star_mul_self u |>.trans <| (mul_star_self u).symm

instance coe_isStarNormal (u : unitary R) : IsStarNormal (u : R) where
  star_comm_self := congr(Subtype.val $(star_comm_self' u))

@[aesop 10% apply (rule_sets := [CStarAlgebra])]
lemma _root_.isStarNormal_of_mem_unitary {u : R} (hu : u ∈ unitary R) : IsStarNormal u :=
  coe_isStarNormal ⟨u, hu⟩

end Monoid

section Map

variable {F R S : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S]
variable [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S] (f : F)

lemma map_mem {r : R} (hr : r ∈ unitary R) : f r ∈ unitary S := by
  rw [unitary.mem_iff] at hr
  simpa [map_star, map_mul] using And.intro congr(f $(hr.1)) congr(f $(hr.2))

/-- The group homomorphism between unitary subgroups of star monoids induced by a star
homomorphism -/
@[simps]
def map : unitary R →* unitary S where
  toFun := Subtype.map f (fun _ ↦ map_mem f)
  map_one' := Subtype.ext <| map_one f
  map_mul' _ _ := Subtype.ext <| map_mul f _ _

lemma toUnits_comp_map : toUnits.comp (map f) = (Units.map f).comp toUnits := by ext; rfl

end Map

section CommMonoid

variable [CommMonoid R] [StarMul R]

instance : CommGroup (unitary R) :=
  { inferInstanceAs (Group (unitary R)), Submonoid.toCommMonoid _ with }

theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[norm_cast]
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
  eq_inv_of_mul_eq_one_right <| coe_mul_star_self _

@[norm_cast]
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]

@[norm_cast]
theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U : R) ^ z := by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]

end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

instance : Neg (unitary R) where
  neg U :=
    ⟨-U, by simp [mem_iff, star_neg, neg_mul_neg]⟩

@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
lemma spectrum.unitary_conjugate {a : A} {u : unitary A} :
    spectrum R (u * a * (star u : A)) = spectrum R a :=
  spectrum.units_conjugate (u := unitary.toUnits u)

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
lemma spectrum.unitary_conjugate' {a : A} {u : unitary A} :
    spectrum R ((star u : A) * a * u) = spectrum R a := by
  simpa using spectrum.unitary_conjugate (u := star u)

end UnitaryConjugate

end unitary
