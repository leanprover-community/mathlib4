/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Ring.Action.End
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!

# Residue Field of local rings

We prove basic properties of the residue field of a local ring.

-/

variable {R S T : Type*}

namespace IsLocalRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

lemma residue_def (x) : residue R x = Ideal.Quotient.mk (maximalIdeal R) x := rfl

lemma ker_residue : RingHom.ker (residue R) = maximalIdeal R :=
  Ideal.mk_ker

@[simp]
lemma residue_eq_zero_iff (x : R) : residue R x = 0 ↔ x ∈ maximalIdeal R := by
  rw [← RingHom.mem_ker, ker_residue]

lemma residue_ne_zero_iff_isUnit (x : R) : residue R x ≠ 0 ↔ IsUnit x := by
  simp

lemma residue_surjective :
    Function.Surjective (IsLocalRing.residue R) :=
  Ideal.Quotient.mk_surjective

variable (R)

instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :
    Algebra R₀ (ResidueField R) :=
  Ideal.Quotient.algebra _

instance {R₁ R₂} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ R₂] [Algebra R₁ R] [Algebra R₂ R] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (IsLocalRing.ResidueField R) := by
  delta IsLocalRing.ResidueField; infer_instance

@[simp]
theorem ResidueField.algebraMap_eq : algebraMap R (ResidueField R) = residue R :=
  rfl

instance : IsLocalHom (IsLocalRing.residue R) :=
  ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Module.Finite R₀ R] :
    Module.Finite R₀ (ResidueField R) :=
  .of_surjective (IsScalarTower.toAlgHom R₀ R _).toLinearMap Ideal.Quotient.mk_surjective

variable {R}

namespace ResidueField

/-- A local ring homomorphism into a field can be descended onto the residue field. -/
def lift {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S) [IsLocalHom f] :
    IsLocalRing.ResidueField R →+* S :=
  Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))

theorem lift_comp_residue {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S)
    [IsLocalHom f] : (lift f).comp (residue R) = f :=
  RingHom.ext fun _ => rfl

@[simp]
theorem lift_residue_apply {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S)
    [IsLocalHom f] (x) : lift f (residue R x) = f x :=
  rfl

/-- The map on residue fields induced by a local homomorphism between local rings -/
noncomputable def map (f : R →+* S) [IsLocalHom f] : ResidueField R →+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    unfold ResidueField
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

/-- Applying `IsLocalRing.ResidueField.map` to the identity ring homomorphism gives the identity
ring homomorphism. -/
@[simp]
theorem map_id :
    IsLocalRing.ResidueField.map (RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl

/-- The composite of two `IsLocalRing.ResidueField.map`s is the `IsLocalRing.ResidueField.map` of
the composite. -/
theorem map_comp (f : T →+* R) (g : R →+* S) [IsLocalHom f] [IsLocalHom g] :
    IsLocalRing.ResidueField.map (g.comp f) =
      (IsLocalRing.ResidueField.map g).comp (IsLocalRing.ResidueField.map f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl

theorem map_comp_residue (f : R →+* S) [IsLocalHom f] :
    (ResidueField.map f).comp (residue R) = (residue S).comp f :=
  rfl

theorem map_residue (f : R →+* S) [IsLocalHom f] (r : R) :
    ResidueField.map f (residue R r) = residue S (f r) :=
  rfl

theorem map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x :=
  DFunLike.congr_fun map_id x

@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : ResidueField R) [IsLocalHom f]
    [IsLocalHom g] : map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp f g).symm x

/-- A ring isomorphism defines an isomorphism of residue fields. -/
@[simps apply]
noncomputable def mapEquiv (f : R ≃+* S) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S where
  toFun := map (f : R →+* S)
  invFun := map (f.symm : S →+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _

@[simp]
theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl

@[simp]
theorem mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  RingEquiv.toRingHom_injective <| map_comp (e₁ : R →+* S) (e₂ : S →+* T)

@[simp]
theorem mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.toRingHom_injective map_id

/-- The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`. -/
@[simps]
noncomputable def mapAut : RingAut R →* RingAut (IsLocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

section MulSemiringAction

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- If `G` acts on `R` as a `MulSemiringAction`, then it also acts on `IsLocalRing.ResidueField R`.
-/
noncomputable instance : MulSemiringAction G (IsLocalRing.ResidueField R) :=
  MulSemiringAction.compHom _ <| mapAut.comp (MulSemiringAction.toRingAut G R)

@[simp]
theorem residue_smul (g : G) (r : R) : residue R (g • r) = g • residue R r :=
  rfl

end MulSemiringAction

section FiniteDimensional

variable [Algebra R S] [IsLocalHom (algebraMap R S)]

noncomputable instance : Algebra (ResidueField R) (ResidueField S) :=
  (ResidueField.map (algebraMap R S)).toAlgebra

instance : IsScalarTower R (ResidueField R) (ResidueField S) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance finite_of_module_finite [Module.Finite R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  .of_restrictScalars_finite R _ _

@[deprecated (since := "2025-01-12")]
alias finiteDimensional_of_noetherian := finite_of_module_finite

lemma finite_of_finite [Module.Finite R S] (hfin : Finite (ResidueField R)) :
    Finite (ResidueField S) := Module.finite_of_finite (ResidueField R)

end FiniteDimensional

end ResidueField

theorem isLocalHom_residue : IsLocalHom (IsLocalRing.residue R) := by
  constructor
  intro a ha
  by_contra h
  rw [residue_def, Ideal.Quotient.eq_zero_iff_mem.mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)]
    at ha
  exact ha.ne_zero rfl

end

end IsLocalRing

@[deprecated (since := "2024-11-11")]
alias LocalRing.ker_residue := IsLocalRing.ker_residue

@[deprecated (since := "2024-11-11")]
alias LocalRing.residue_eq_zero_iff := IsLocalRing.residue_eq_zero_iff

@[deprecated (since := "2024-11-11")]
alias LocalRing.residue_ne_zero_iff_isUnit := IsLocalRing.residue_ne_zero_iff_isUnit

@[deprecated (since := "2024-11-11")]
alias LocalRing.residue_surjective := IsLocalRing.residue_surjective

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.algebraMap_eq := IsLocalRing.ResidueField.algebraMap_eq

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.lift := IsLocalRing.ResidueField.lift

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.lift_comp_residue := IsLocalRing.ResidueField.lift_comp_residue

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.lift_residue_apply := IsLocalRing.ResidueField.lift_residue_apply

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map := IsLocalRing.ResidueField.map

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_id := IsLocalRing.ResidueField.map_id

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_comp := IsLocalRing.ResidueField.map_comp

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_comp_residue := IsLocalRing.ResidueField.map_comp_residue

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_residue := IsLocalRing.ResidueField.map_residue

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_id_apply := IsLocalRing.ResidueField.map_id_apply

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.map_map := IsLocalRing.ResidueField.map_map

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.mapEquiv := IsLocalRing.ResidueField.mapEquiv

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.mapEquiv.symm := IsLocalRing.ResidueField.mapEquiv.symm

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.mapEquiv_trans := IsLocalRing.ResidueField.mapEquiv_trans

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.mapEquiv_refl := IsLocalRing.ResidueField.mapEquiv_refl

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.mapAut := IsLocalRing.ResidueField.mapAut

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.residue_smul := IsLocalRing.ResidueField.residue_smul

@[deprecated (since := "2024-11-11")]
alias LocalRing.ResidueField.finite_of_finite := IsLocalRing.ResidueField.finite_of_finite
