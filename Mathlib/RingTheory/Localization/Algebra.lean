/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization of algebra maps

In this file we provide constructors to localize algebra maps. Also we show that
localization commutes with taking kernels for ring homomorphisms.

## Implementation detail

The proof that localization commutes with taking kernels does not use the result for linear maps,
as the translation is currently tedious and can be unified easily after the localization refactor.

-/

universe u u' v v' w w'

variable {R S P : Type*} (Q : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]
  [CommSemiring Q]
  {M : Submonoid R} {T : Submonoid P}
  [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
  (g : R →+* P)

variable (M S) in
/-- The span of `I` in a localization of `R` at `M` is the localization of `I` at `M`. -/
instance Algebra.idealMap_isLocalizedModule (I : Ideal R) :
    IsLocalizedModule M (Algebra.idealMap I (S := S)) where
  map_units x := by
    rw [isUnit_iff_exists]
    have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
    let φ : Module.End R
        (I.map (algebraMap R S)) := {
      toFun := fun y ↦ ⟨hu.unit⁻¹ * y, by simp⟩
      map_add' := fun x y ↦ by simp [mul_add]
      map_smul' := fun a x ↦ by simp
    }
    refine ⟨φ, ?_, ?_⟩
    · ext y
      simp [φ, Algebra.smul_def, ← mul_assoc]
    · ext y
      simp [φ, Algebra.smul_def, ← mul_assoc]
  surj' y := by
    obtain ⟨x, hx⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp y.property
    use x
    apply Subtype.ext
    simp [Submonoid.smul_def, Algebra.smul_def, mul_comm, hx]
  exists_of_eq h := by
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) (congrArg Subtype.val h)
    exact ⟨c, Subtype.ext hc⟩

lemma IsLocalization.ker_map (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S →+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

variable (S) in
/-- The canonical linear map from the kernel of `g` to the kernel of its localization. -/
def RingHom.toKerIsLocalization (hy : M ≤ Submonoid.comap g T) :
    RingHom.ker g →ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S →+* Q) where
  toFun x := ⟨algebraMap R S x, by simp [RingHom.mem_ker, (RingHom.mem_ker g).mp x.property]⟩
  map_add' x y := by
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add, AddSubmonoid.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, RingHom.id_apply,
      SetLike.mk_smul_of_tower_mk, Algebra.smul_def]

@[simp]
lemma RingHom.toKerIsLocalization_apply (hy : M ≤ Submonoid.comap g T) (r : RingHom.ker g) :
    (RingHom.toKerIsLocalization S Q g hy r).val = algebraMap R S r :=
  rfl

/-- The canonical linear map from the kernel of `g` to the kernel of its localization
is localizing. In other words, localization commutes with taking kernels. -/
lemma RingHom.toKerIsLocalization_isLocalizedModule (hT : Submonoid.map g M = T) :
    IsLocalizedModule M (toKerIsLocalization S Q g (hT.symm ▸ Submonoid.le_comap_map M)) := by
  let e := LinearEquiv.ofEq _ _ (IsLocalization.ker_map (S := S) Q g hT).symm
  convert_to IsLocalizedModule M ((e.restrictScalars R).toLinearMap ∘ₗ
    Algebra.idealMap S (RingHom.ker g))
  apply IsLocalizedModule.of_linearEquiv

section Algebra

open Algebra

variable {R : Type u} [CommRing R] (M : Submonoid R)
variable {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]
variable {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization M Rₚ]
variable {Aₚ : Type v'} [CommRing Aₚ] [Algebra R Aₚ] [Algebra A Aₚ] [IsScalarTower R A Aₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₚ]
variable {Bₚ : Type v'} [CommRing Bₚ] [Algebra R Bₚ] [Algebra B Bₚ] [IsScalarTower R B Bₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₚ]
variable [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]

namespace IsLocalization

/-- An algebra map `A →ₐ[R] B` induces an algebra map on localizations `Aₚ →ₐ[Rₚ] Bₚ`. -/
noncomputable def mapₐ (f : A →ₐ[R] B) : Aₚ →ₐ[Rₚ] Bₚ :=
  ⟨IsLocalization.map Bₚ f.toRingHom (Algebra.algebraMapSubmonoid_le_comap M f), fun r ↦ by
    obtain ⟨a, m, rfl⟩ := IsLocalization.mk'_surjective M r
    simp [algebraMap_mk' (S := A), algebraMap_mk' (S := B), map_mk']⟩

@[simp]
lemma mapₐ_apply (f : A →ₐ[R] B) (x : Aₚ) :
    (mapₐ M f : Aₚ →ₐ[Rₚ] Bₚ) x = map Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) x :=
  rfl

lemma isLocalization_algebraMapSubmonoid_map_algHom (f : A →ₐ[R] B) :
    IsLocalization ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ := by
  erw [algebraMapSubmonoid_map_eq M f]
  infer_instance

lemma mapₐ_injective_of_injective (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (mapₐ M f : Aₚ →ₐ[Rₚ] Bₚ) :=
  haveI : IsLocalization ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ :=
    isLocalization_algebraMapSubmonoid_map_algHom M f
  IsLocalization.map_injective_of_injective _ _ _ hf

lemma mapₐ_surjective_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    Function.Surjective (mapₐ M f : Aₚ →ₐ[Rₚ] Bₚ) :=
  haveI : IsLocalization ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ :=
    isLocalization_algebraMapSubmonoid_map_algHom M f
  IsLocalization.map_surjective_of_surjective _ _ _ hf

end IsLocalization

open IsLocalization

variable (Rₚ) (Aₚ) (Bₚ)

/-- The canonical linear map from the kernel of an algebra homomorphism to its localization. -/
def AlgHom.toKerIsLocalization (f : A →ₐ[R] B) :
    RingHom.ker f →ₗ[A] RingHom.ker (mapₐ M f : Aₚ →ₐ[Rₚ] Bₚ) :=
  RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f)

@[simp]
lemma AlgHom.toKerIsLocalization_apply (f : A →ₐ[R] B) (x : RingHom.ker f) :
    AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f x =
      RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) x :=
  rfl

/-- The canonical linear map from the kernel of an algebra homomorphism to its localization
is localizing. -/
lemma AlgHom.toKerIsLocalization_isLocalizedModule (f : A →ₐ[R] B) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A M)
      (AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f) :=
  RingHom.toKerIsLocalization_isLocalizedModule Bₚ f.toRingHom
    (algebraMapSubmonoid_map_eq M f)

end Algebra
