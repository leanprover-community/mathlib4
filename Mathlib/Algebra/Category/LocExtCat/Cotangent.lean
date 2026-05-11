/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocExtCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Cotangent Spaces in `LocExtCat`

This file contains results about cotangent spaces for objects in the category of
local extensions over `Λ` with a fixed residue field `k`.

## Main Results

* `LocExtCat.mapCotangent`: The canonical `k`-linear map between cotangent spaces of
  the underlying extions induced by a morphism `f : A ⟶ B` in `LocExtCat`.

* `LocExtCat.surjective_mapCotangent_toOfQuot`: The cotangent map induced by a surjective morphism
  is surjective.

* `LocExtCat.baseCotangentMap`: The canonical linear map from the cotangent space
  of the base ring `Λ` to the cotangent space of `A`.

* `LocExtCat.exact_baseCotangentMap_mapCotangent_toSpecialFiber`: The exactness of
  the conormal sequence for the special fiber.

-/

@[expose] public section

noncomputable section

universe v u

open IsLocalRing Function TensorProduct CategoryTheory KaehlerDifferential Algebra.Extension

namespace LocExtCat

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {A B C : LocExtCat Λ k}

section mapCotangent

/-- A morphism in `LocExtCat` induces a map between cotangent spaces of
the underlying extensions. -/
abbrev mapCotangent (f : A ⟶ B) : A.Cotangent →ₗ[k] B.Cotangent :=
  Cotangent.map f.hom

@[simp]
lemma mapCotangent_id : mapCotangent (𝟙 A) = LinearMap.id := Cotangent.map_id

lemma mapCotangent_comp (f : A ⟶ B) (g : B ⟶ C) :
    mapCotangent (f ≫ g) = mapCotangent g ∘ₗ mapCotangent f :=
  Cotangent.map_comp C.toExtension f.hom g.hom

/-- The `k`-linear equivalence between cotangent spaces induced by
an isomorphism in `LocAlgCat`. -/
def equivCotangent (e : A ≅ B) : A.Cotangent ≃ₗ[k] B.Cotangent where
  __ := mapCotangent e.hom
  invFun := mapCotangent e.inv
  left_inv _ := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]
  right_inv _ := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]

@[simp]
lemma equivCotangent_apply (e : A ≅ B) (x : A.Cotangent) :
    equivCotangent e x = mapCotangent e.hom x := rfl

@[simp]
lemma equivCotangent_symm_apply (e : A ≅ B) (x : B.Cotangent) :
    (equivCotangent e).symm x = mapCotangent e.inv x := rfl

private lemma comap_hom_toRingHom_ker_eq (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Ideal.comap (Hom.hom (A.toOfQuot I)).toRingHom (A.ofQuot I).ker =
      RingHom.ker (Hom.hom (A.toOfQuot I)).toRingHom ⊔ A.ker := by
  simp only [ker_extension]
  have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective.isLocalHom
  change Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (A ⧸ I)) =
    RingHom.ker (Ideal.Quotient.mk I) ⊔ _
  rw [maximalIdeal_comap, Ideal.mk_ker, right_eq_sup]
  exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)

theorem surjective_mapCotangent_toOfQuot (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Surjective (mapCotangent (A.toOfQuot I)) :=
  Cotangent.map_surjective_of_comap_eq (A.toOfQuot I).hom Ideal.Quotient.mk_surjective
    (comap_hom_toRingHom_ker_eq I)

open Submodule in
theorem bijective_mapCotangent_toOfQuot_iff (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Bijective (mapCotangent (A.toOfQuot I)) ↔ I ≤ maximalIdeal A ^ 2 := by
  simp only [Bijective, surjective_mapCotangent_toOfQuot I, and_true, ← LinearMap.ker_eq_bot]
  rw [← Submodule.restrictScalars_inj A.Ring, Cotangent.map_ker_of_surjective _
    Ideal.Quotient.mk_surjective (comap_hom_toRingHom_ker_eq I)]
  simp only [ker_toRingHom_toOfQuot, ker_extension, comap_inf, comap_subtype_le_iff, Std.le_refl,
    inf_of_le_left, inf_le_left, restrictScalars_bot]
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, Cotangent.ker_mk,
    ← map_le_map_iff_of_injective (subtype_injective _), map_comap_eq, range_subtype,
    ker_extension, map_smul'', Submodule.map_top, smul_eq_mul, range_subtype, ← pow_two,
    ← right_eq_inf.mpr (le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›))]

@[stacks 06S3 "(1) => (2)"]
theorem surjective_mapCotangent_of_surjective {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    Surjective (mapCotangent f) := by
  rw [← toOfQuot_comp_ofQuotKerIsoOfSurjective_hom h, mapCotangent_comp, LinearMap.coe_comp]
  exact Function.Surjective.comp (equivCotangent (ofQuotKerIsoOfSurjective f h)).surjective
    (surjective_mapCotangent_toOfQuot _)

theorem bijective_mapCotangent_iff {f : A ⟶ B} (hf : Surjective f.toAlgHom) :
    Function.Bijective (mapCotangent f) ↔ RingHom.ker f.toAlgHom ≤ maximalIdeal A ^ 2 := by
  nth_rw 1 [← bijective_mapCotangent_toOfQuot_iff, ← toOfQuot_comp_ofQuotKerIsoOfSurjective_hom hf,
    mapCotangent_comp, LinearMap.coe_comp, Bijective.of_comp_iff']
  exact (equivCotangent (ofQuotKerIsoOfSurjective f hf)).bijective

@[stacks 06S3 "(2) => (3)"]
theorem mapCotangent_mapOfQuot_surjective_of_mapCotangent_surjective {I : Ideal A} {J : Ideal B}
    {f : A ⟶ B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.toAlgHom)
    (h : Surjective (mapCotangent f)) : Surjective (mapCotangent (mapOfQuot f hf)) := by
  have : Surjective ((mapCotangent (mapOfQuot f hf)) ∘ₗ (mapCotangent (A.toOfQuot I))) := by
    rw [← mapCotangent_comp, toOfQuot_comp_mapOfQuot, mapCotangent_comp, LinearMap.coe_comp]
    exact .comp (surjective_mapCotangent_toOfQuot J) h
  exact .of_comp this

open Submodule in
@[stacks 06GZ "(2) => (1)"]
theorem surjective_of_surjective_mapCotangent [IsPrecomplete (maximalIdeal A) A]
    [IsNoetherianRing B] [haus : IsHausdorff (maximalIdeal B) B] (f : A ⟶ B)
    (h : Surjective (mapCotangent f)) : Surjective f.toAlgHom := by
  have map_eq : (maximalIdeal A).map f.toAlgHom = maximalIdeal B := by
    refine le_antisymm f.map_maximalIdeal_le ?_
    rw [← comap_subtype_eq_top, ← CotangentSpace.map_eq_top_iff, eq_top_iff']
    intro x
    obtain ⟨⟨x, x_in⟩, rfl⟩ := (maximalIdeal B).toCotangent_surjective x
    obtain ⟨y, hy⟩ := h (Cotangent.mk ⟨x, B.ker_extension ▸ x_in⟩)
    obtain ⟨y, rfl⟩ := Cotangent.mk_surjective y
    simp only [Cotangent.map_mk, Hom.toAlgHom_apply, Cotangent.mk_eq_mk_iff_sub_mem] at hy
    suffices ∃ a ∈ Ideal.map (Hom.toAlgHom f) A.ker, a ∈ B.ker ∧ a - x ∈ B.ker ^ 2 by
      simpa [Ideal.toCotangent_eq]
    refine ⟨f.toAlgHom y, Ideal.mem_map_of_mem _ y.prop, ?_, hy⟩
    rw [ker_extension, ← Ideal.mem_comap, f.comap_maximalIdeal_eq, ← ker_extension]
    exact y.prop
  rw [← map_eq, ← Ideal.map_coe, ← AlgHom.toRingHom_eq_coe] at haus
  refine surjective_of_mk_map_comp_surjective (I := maximalIdeal A) _ fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := A.residue_surjective (B.residue y)
  exact ⟨x, by rw [RingHom.comp_apply, Ideal.Quotient.eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.map_coe, map_eq, ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hx, ← AlgHom.comp_apply,
    f.residue_comp]⟩

end mapCotangent

section specialFiber

open LinearMap

variable [IsLocalRing Λ] [Algebra.IsIntegral Λ k]

theorem surjective_mapCotangent_toSpecialFiber : Surjective (mapCotangent A.toSpecialFiber) :=
  surjective_mapCotangent_toOfQuot _

/-- The canonical linear map from the cotangent space of `Λ` to the cotangent space of `A`. -/
def baseCotangentMap (A : LocExtCat Λ k) : CotangentSpace Λ →ₗ[Λ] A.Cotangent :=
  (cotangentEquivCotangentKer.symm.toLinearMap.restrictScalars Λ).comp <|
    (maximalIdeal Λ).mapCotangent A.ker (Algebra.ofId Λ A) (by rw [← Ideal.comap_coe,
      Algebra.toRingHom_ofId, ker_extension, comap_algebraMap_maximalIdeal])

@[simp]
lemma baseCotangentMap_toCotangent (x : maximalIdeal Λ) :
    A.baseCotangentMap ((maximalIdeal Λ).toCotangent x) = Cotangent.mk ⟨algebraMap Λ A x, by
      have := isLocalHom_algebraMap A
      rw [← Ideal.mem_comap, ker_extension, maximalIdeal_comap]
      exact x.prop⟩ := rfl

theorem range_baseCotangentMap_le (A : LocExtCat Λ k) :
    A.baseCotangentMap.range ≤ A.cotangentComplex.ker.restrictScalars Λ := by
  intro x hx
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rcases hx with ⟨y, hy⟩
  rw [Submodule.restrictScalars_mem, mem_ker, ← hy]
  obtain ⟨y, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective y
  simp

lemma mapCotangent_comp_liftBaseChange_baseCotangentMap (f : A ⟶ B) :
    (mapCotangent f).comp (liftBaseChange k A.baseCotangentMap) =
      liftBaseChange k B.baseCotangentMap := by
  ext x
  obtain ⟨x, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective x
  simp

open Submodule in
theorem range_liftBaseChange_baseCotangentMap :
    (liftBaseChange k A.baseCotangentMap).range = (mapCotangent A.toSpecialFiber).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    rcases hx with ⟨y, hy⟩; rw [← hy]
    clear * -; induction y with
    | zero => simp
    | tmul x y =>
      obtain ⟨y, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective y
      simp [(mk_eq_zero ..).mpr]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · rw [← restrictScalars_mem A, Cotangent.map_ker_of_surjective _ Ideal.Quotient.mk_surjective <|
        comap_hom_toRingHom_ker_eq ((maximalIdeal Λ).map (algebraMap Λ A)), ker_toRingHom_toOfQuot,
      comap_inf, comap_subtype_self, inf_top_eq, mem_map] at hx
    obtain ⟨⟨x, x_in⟩, rfl⟩ := Cotangent.mk_surjective x
    simp only [mem_comap, subtype_apply, Subtype.exists, ker_extension, exists_and_left] at hx
    rcases hx with ⟨y, y_in, y_in', hy⟩
    rw [← hy]; clear * - y_in
    have : IsLocalHom (algebraMap Λ A) := isLocalHom_algebraMap A
    induction y_in using span_induction with
    | mem x h =>
      obtain ⟨r, r_in, rfl⟩ := h
      exact ⟨1 ⊗ₜ (maximalIdeal Λ).toCotangent ⟨r, r_in⟩, by simp⟩
    | zero => simp only [(mk_eq_zero ..).mpr, map_zero, zero_mem]
    | add u v hu hv ihu ihv =>
      exact add_mem (ihu (map_maximalIdeal_le _ hu)) (ihv (map_maximalIdeal_le _ hv))
    | smul a x hx ih =>
      rw [← SetLike.mk_smul_mk _ _ _ (A.ker_extension ▸ map_maximalIdeal_le _ hx), map_smul,
        algebra_compatible_smul k]
      exact smul_mem _ _ (ih (map_maximalIdeal_le _ hx))

theorem exact_liftBaseChange_baseCotangentMap_mapCotangent_toSpecialFiber :
    Exact (liftBaseChange k A.baseCotangentMap) (mapCotangent A.toSpecialFiber) :=
  LinearMap.exact_iff.mpr A.range_liftBaseChange_baseCotangentMap.symm

@[stacks 06S3 "(3) => (2)"]
theorem surjective_mapCotangent_of_surjective_mapCotangent_mapSpecialFiber
    (f : A ⟶ B) (h : Surjective (mapCotangent (mapSpecialFiber f))) :
    Surjective (mapCotangent f) := fun y ↦ by
  obtain ⟨x, hx⟩ := h (mapCotangent B.toSpecialFiber y)
  obtain ⟨x, rfl⟩ := surjective_mapCotangent_toSpecialFiber x
  rw [← LinearMap.comp_apply, ← mapCotangent_comp, toOfQuot_comp_mapOfQuot,
    mapCotangent_comp, LinearMap.comp_apply] at hx
  have h_ker : y - mapCotangent f x ∈ LinearMap.ker (mapCotangent B.toSpecialFiber) := by
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  rw [← range_liftBaseChange_baseCotangentMap, LinearMap.mem_range] at h_ker
  rcases h_ker with ⟨z, hz⟩
  use x + liftBaseChange k A.baseCotangentMap z
  rw [map_add, ← LinearMap.comp_apply, mapCotangent_comp_liftBaseChange_baseCotangentMap, hz,
    add_sub_cancel]

end specialFiber

end LocExtCat
