/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Star.MonoidHom
import Mathlib.Algebra.Star.StarProjection

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

/-- For unitary `U` in a star-monoid `R`, `x * U = y * U` if and only if `x = y`
for all `x` and `y` in `R`. -/
protected theorem mul_left_inj {x y : R} (U : unitary R) :
    x * U = y * U ↔ x = y :=
  unitary.val_toUnits_apply U ▸ Units.mul_left_inj _

/-- For unitary `U` in a star-monoid `R`, `U * x = U * y` if and only if `x = y`
for all `x` and `y` in `R`. -/
protected theorem mul_right_inj {x y : R} (U : unitary R) :
    U * x = U * y ↔ x = y :=
  unitary.val_toUnits_apply U ▸ Units.mul_right_inj _

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

end unitary

section Group

variable {G : Type*} [Group G] [StarMul G]

theorem unitary.inv_mem {g : G} (hg : g ∈ unitary G) : g⁻¹ ∈ unitary G := by
  simp_rw [unitary.mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

variable (G) in
/-- `unitary` as a `Subgroup` of a group.

Note the group structure on this type is not defeq to the one on `unitary`.
This situation naturally arises when considering the unitary elements as a
subgroup of the group of units of a star monoid. -/
def unitarySubgroup : Subgroup G where
  toSubmonoid := unitary G
  inv_mem' := unitary.inv_mem

@[simp]
theorem unitarySubgroup_toSubmonoid : (unitarySubgroup G).toSubmonoid = unitary G := rfl

@[simp]
theorem mem_unitarySubgroup_iff {g : G} : g ∈ unitarySubgroup G ↔ g ∈ unitary G :=
  Iff.rfl

nonrec theorem unitary.inv_mem_iff {g : G} : g⁻¹ ∈ unitary G ↔ g ∈ unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

end Group

namespace unitary

section SMul

section

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

lemma smul_mem_of_mem {r : R} {a : A} (hr : r ∈ unitary R) (ha : a ∈ unitary A) :
    r • a ∈ unitary A := by
  simp [mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]

lemma smul_mem (r : unitary R) {a : A} (ha : a ∈ unitary A) :
    r • a ∈ unitary A :=
  smul_mem_of_mem (R := R) r.prop ha

instance : SMul (unitary R) (unitary A) where
  smul r a := ⟨r • a, smul_mem r a.prop⟩

@[simp, norm_cast]
lemma coe_smul (r : unitary R) (a : unitary A) : ↑(r • a) = r • (a : A) := rfl

instance : MulAction (unitary R) (unitary A) where
  one_smul _ := Subtype.ext <| one_smul ..
  mul_smul _ _ _ := Subtype.ext <| mul_smul ..

instance : StarModule (unitary R) (unitary A) where
  star_smul _ _ := Subtype.ext <| star_smul (_ : R) _

end

section

variable {S A : Type*}
  [Monoid R] [Monoid S] [Monoid A] [StarMul R] [StarMul S] [StarMul A]
  [MulAction R S] [MulAction R A] [MulAction S A]
  [StarModule R S] [StarModule R A] [StarModule S A]
  [IsScalarTower R A A] [IsScalarTower S A A]
  [SMulCommClass R A A] [SMulCommClass S A A]

instance [SMulCommClass R S A] : SMulCommClass (unitary R) (unitary S) (unitary A) where
  smul_comm _ _ _ := Subtype.ext <| smul_comm _ (_ : S) (_ : A)

instance [IsScalarTower R S S] [SMulCommClass R S S] [IsScalarTower R S A] :
    IsScalarTower (unitary R) (unitary S) (unitary A) where
  smul_assoc _ _ _ := Subtype.ext <| smul_assoc _ (_ : S) (_ : A)

end

end SMul

section Map

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

lemma map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S]
    (f : F) {r : R} (hr : r ∈ unitary R) : f r ∈ unitary S := by
  rw [unitary.mem_iff] at hr
  simpa [map_star, map_mul] using And.intro congr(f $(hr.1)) congr(f $(hr.2))

/-- The star monoid homomorphism between unitary subgroups induced by a star monoid homomorphism of
the underlying star monoids. -/
@[simps]
def map (f : R →⋆* S) : unitary R →⋆* unitary S where
  toFun := Subtype.map f (fun _ ↦ map_mem f)
  map_one' := Subtype.ext <| map_one f
  map_mul' _ _ := Subtype.ext <| map_mul f _ _
  map_star' _ := Subtype.ext <| map_star f _

@[simp]
lemma coe_map (f : R →⋆* S) (x : unitary R) : map f x = f x := rfl

@[simp]
lemma coe_map_star (f : R →⋆* S) (x : unitary R) : map f (star x) = f (star x) := rfl

@[simp]
lemma map_id : map (.id R) = .id (unitary R) := rfl

lemma map_comp (g : S →⋆* T) (f : R →⋆* S) : map (g.comp f) = (map g).comp (map f) := rfl

@[simp]
lemma map_injective {f : R →⋆* S} (hf : Function.Injective f) :
    Function.Injective (map f : unitary R → unitary S) :=
  Subtype.map_injective (fun _ ↦ map_mem f) hf

lemma toUnits_comp_map (f : R →⋆* S) :
    toUnits.comp (map f).toMonoidHom = (Units.map f.toMonoidHom).comp toUnits := by
  ext; rfl

/-- The star monoid isomorphism between unitary subgroups induced by a star monoid isomorphism of
the underlying star monoids. -/
@[simps]
def mapEquiv (f : R ≃⋆* S) : unitary R ≃⋆* unitary S :=
  { map f.toStarMonoidHom with
    toFun := map f.toStarMonoidHom
    invFun := map f.symm.toStarMonoidHom
    left_inv := fun _ ↦ Subtype.ext <| f.left_inv _
    right_inv := fun _ ↦ Subtype.ext <| f.right_inv _ }

@[simp]
lemma mapEquiv_refl : mapEquiv (.refl R) = .refl (unitary R) := rfl

@[simp]
lemma mapEquiv_symm (f : R ≃⋆* S) : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
lemma mapEquiv_trans (f : R ≃⋆* S) (g : S ≃⋆* T) :
    mapEquiv (f.trans g) = (mapEquiv f).trans (mapEquiv g) :=
  rfl

@[simp]
lemma toMonoidHom_mapEquiv (f : R ≃⋆* S) :
    (mapEquiv f).toStarMonoidHom = map f.toStarMonoidHom :=
  rfl

/-- The unitary subgroup of the units is equivalent to the unitary elements of the monoid. -/
@[simps!]
def _root_.unitarySubgroupUnitsEquiv {M : Type*} [Monoid M] [StarMul M] :
    unitarySubgroup Mˣ ≃* unitary M where
  toFun x := ⟨x.val, congr_arg Units.val x.prop.1, congr_arg Units.val x.prop.2⟩
  invFun x := ⟨⟨x, star x, x.prop.2, x.prop.1⟩, Units.ext x.prop.1, Units.ext x.prop.2⟩
  map_mul' _ _ := rfl
  left_inv _ := Subtype.ext <| Units.ext rfl
  right_inv _ := rfl

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
    ⟨-U, by simp [mem_iff, star_neg]⟩

@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
lemma spectrum_star_right_conjugate {a : A} {U : unitary A} :
    spectrum R (U * a * (star U : A)) = spectrum R a :=
  spectrum.units_conjugate (u := unitary.toUnits U)

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
lemma spectrum_star_left_conjugate {a : A} {U : unitary A} :
    spectrum R ((star U : A) * a * U) = spectrum R a := by
  simpa using spectrum_star_right_conjugate (U := star U)

@[deprecated (since := "2025-10-20")] alias spectrum.unitary_conjugate :=
  spectrum_star_right_conjugate
@[deprecated (since := "2025-10-20")] alias spectrum.unitary_conjugate' :=
  spectrum_star_left_conjugate

end UnitaryConjugate

end unitary

theorem IsStarProjection.two_mul_sub_one_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 2 * p - 1 ∈ unitary R := by
  simp only [two_mul, unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]
