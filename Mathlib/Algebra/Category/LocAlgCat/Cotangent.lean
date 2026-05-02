/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Cotangent Spaces in `LocAlgCat`

This file contains results about cotangent spaces for objects in the category of local `Λ`-algebras
with a fixed residue field `k`. It introduces the canonical `k`-vector space structures,
induced linear maps, and exactness properties.

## Main Results

* `LocAlgCat.mapCotangent`: The canonical `k`-linear map between cotangent spaces induced by
  a morphism `f : A ⟶ B` in `LocAlgCat`.

* `LocAlgCat.surjective_mapCotangent_toOfQuot`: The cotangent map induced by a surjective morphism
  is surjective.

* `LocAlgCat.baseCotangentMap`: The canonical linear map from the cotangent space
  of the base ring `Λ` to the cotangent space of `A`.

* `LocAlgCat.exact_baseCotangentMap_mapCotangent_toSpecialFiber`: The exactness of
  the conormal sequence for the special fiber.

-/

@[expose] public section

noncomputable section

universe w v u

open IsLocalRing Function TensorProduct CategoryTheory KaehlerDifferential Algebra

namespace LocAlgCat

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k] {A B C : LocAlgCat.{w} Λ k}

instance module_cotangentSpace : Module k (CotangentSpace A) :=
  fast_instance% .compHom _ (A.residueEquiv.symm : k →+* ResidueField A)

lemma smul_cotangent_def (r : k) (x : CotangentSpace A) : r • x = (A.residueEquiv.symm r) • x :=
  rfl

lemma residue_smul_cotangent (a : A) (x : CotangentSpace A) : A.residue a • x = a • x := by
  rw [← residueEquiv_residue_apply, smul_cotangent_def, AlgEquiv.symm_apply_apply,
    ← IsLocalRing.ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul]

instance : IsScalarTower A k (CotangentSpace A) := .of_algebraMap_smul residue_smul_cotangent

instance : IsScalarTower Λ (ResidueField A) (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [IsScalarTower.algebraMap_apply Λ A, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

instance : IsScalarTower Λ k (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [smul_cotangent_def, IsScalarTower.algebraMap_eq Λ A, RingHom.comp_apply]
  have := residueEquiv_residue_apply (x := algebraMap Λ A r)
  rw [← AlgEquiv.eq_symm_apply, residue_apply] at this
  rw [← this, ← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

/-- The canonical `k`-linear map between cotangent spaces induced by a morphism in `LocAlgCat`. -/
def mapCotangent (f : A ⟶ B) : CotangentSpace A →ₗ[k] CotangentSpace B where
  toFun x := (maximalIdeal A).mapCotangent (maximalIdeal B) f.toAlgHom
    (by rw [f.comap_maximalIdeal_eq]) x
  map_add' := by simp
  map_smul' r x := by
    obtain ⟨s, hs⟩ := A.residue_surjective r
    obtain ⟨t, ht⟩ := B.residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    nth_rw 1 [← hs, ← ht]
    rw [residue_smul_cotangent, ← map_smul, Ideal.mapCotangent_toCotangent, RingHom.id_apply,
      residue_smul_cotangent, Ideal.mapCotangent_toCotangent, ← map_smul, Ideal.toCotangent_eq]
    simp only [pow_two, SetLike.val_smul, smul_eq_mul, map_mul, ← sub_mul]
    refine Ideal.mul_mem_mul ?_ ?_
    · rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← AlgHom.comp_apply, f.residue_comp, ht]
    · rw [← Ideal.mem_comap, f.comap_maximalIdeal_eq]
      exact x.prop

@[simp]
lemma mapCotangent_toCotangent (f : A ⟶ B) (a : maximalIdeal A) :
    mapCotangent f ((maximalIdeal A).toCotangent a) = (maximalIdeal B).toCotangent ⟨f.toAlgHom a,
      by rw [← Ideal.mem_comap, f.comap_maximalIdeal_eq]; exact a.prop⟩ := by simp [mapCotangent]

lemma mapCotangent_comp (f : A ⟶ B) (g : B ⟶ C) :
    mapCotangent (f ≫ g) = mapCotangent g ∘ₗ mapCotangent f := LinearMap.ext fun _ ↦ by
  simp [mapCotangent, ← LinearMap.comp_apply, ← Ideal.mapCotangent_comp]

@[simp]
lemma mapCotangent_id (A : LocAlgCat Λ k) : mapCotangent (𝟙 A) = LinearMap.id := by
  ext x
  rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
  simp

/-- The `k`-linear equivalence between cotangent spaces induced by
an isomorphism in `LocAlgCat`. -/
def equivCotangent (e : A ≅ B) : CotangentSpace A ≃ₗ[k] CotangentSpace B where
  __ := mapCotangent e.hom
  invFun := mapCotangent e.inv
  left_inv x := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]
  right_inv y := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]

@[simp]
lemma equivCotangent_apply (e : A ≅ B) (x : CotangentSpace A) :
    equivCotangent e x = mapCotangent e.hom x := rfl

@[simp]
lemma equivCotangent_symm_apply (e : A ≅ B) (y : CotangentSpace B) :
    (equivCotangent e).symm y = mapCotangent e.inv y := rfl

theorem surjective_mapCotangent_toOfQuot (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Surjective (mapCotangent (A.toOfQuot I)) := by
  have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap A (A ⧸ I)) :=
    ⟨Ideal.Quotient.mk_surjective.isLocalHom.map_nonunit⟩
  change Surjective ((maximalIdeal A).mapCotangent (maximalIdeal (A ⧸ I)) (Algebra.ofId A (A ⧸ I))
    (by rw [← Ideal.comap_coe, Algebra.toRingHom_ofId, maximalIdeal_comap]))
  refine Ideal.mapCotangent_surjective_of_comap_eq (fun _ ↦ Ideal.Quotient.mk_surjective _) ?_
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, ← Ideal.Quotient.algebraMap_eq,
    maximalIdeal_comap, right_eq_sup]
  exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)

open Submodule in
theorem bijective_mapCotangent_toOfQuot_iff (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Bijective (mapCotangent (A.toOfQuot I)) ↔ I ≤ maximalIdeal A ^ 2 := by
  have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap A (A ⧸ I)) :=
    ⟨Ideal.Quotient.mk_surjective.isLocalHom.map_nonunit⟩
  have I_le : I ≤ maximalIdeal A :=
    le_maximalIdeal (J := I) (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  simp only [Bijective, surjective_mapCotangent_toOfQuot I, and_true]
  change Injective ((maximalIdeal A).mapCotangent (maximalIdeal (A ⧸ I)) (Algebra.ofId A (A ⧸ I))
    (by rw [← Ideal.comap_coe, Algebra.toRingHom_ofId, maximalIdeal_comap])) ↔ _
  rw [← LinearMap.ker_eq_bot, Ideal.mapCotangent_ker_of_surjective Ideal.Quotient.mk_surjective (by
    rwa [maximalIdeal_comap, right_eq_sup, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]),
    Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, ← left_eq_inf.mpr I_le,
    ← (comap_injective_of_surjective (maximalIdeal A).toCotangent_surjective).eq_iff,
    comap_map_eq, ← LinearMap.ker, eq_comm, right_eq_sup,
    ← map_le_map_iff_of_injective (subtype_injective _), map_comap_eq, Ideal.map_toCotangent_ker,
    ← right_eq_inf.mpr (by rwa [range_subtype])]

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

@[stacks 06GZ "(2) => (1)"]
theorem surjective_of_surjective_mapCotangent [IsPrecomplete (maximalIdeal A) A]
    [IsNoetherianRing B] [haus : IsHausdorff (maximalIdeal B) B] (f : A ⟶ B)
    (h : Surjective (mapCotangent f)) : Surjective f.toAlgHom := by
  have map_eq : (maximalIdeal A).map f.toAlgHom = maximalIdeal B := by
    refine le_antisymm f.map_maximalIdeal_le ?_
    rw [← Submodule.comap_subtype_eq_top, ← CotangentSpace.map_eq_top_iff, Submodule.eq_top_iff']
    intro x; obtain ⟨x, rfl⟩ := h x
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    exact Submodule.mem_map_of_mem <| Ideal.mem_map_of_mem f.toAlgHom x.prop
  rw [← map_eq, ← Ideal.map_coe, ← AlgHom.toRingHom_eq_coe] at haus
  refine surjective_of_mk_map_comp_surjective (I := maximalIdeal A) _ fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := A.residue_surjective (B.residue y)
  exact ⟨x, by rw [RingHom.comp_apply, Ideal.Quotient.eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.map_coe, map_eq, ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hx, ← AlgHom.comp_apply,
    f.residue_comp]⟩

/-- The relative cotangent space for an object in `LocAlgCat`. -/
@[stacks 06GY]
abbrev RelCotangent (A : LocAlgCat.{w} Λ k) : Type _ := k ⊗[A] Ω[A⁄Λ]

/-- The canonical `k`-linear map between relative cotangent spaces
induced by a morphism in `LocAlgCat`. -/
def mapRelCotangent (f : A ⟶ B) : A.RelCotangent →ₗ[k] B.RelCotangent :=
  letI := f.relativeAlgebra
  haveI := f.isScalarTower'_relativeAlgebra
  letI F : k →ₗ[k] Ω[A⁄Λ] →ₗ[A] B.RelCotangent := .mk₂' k A (fun (r : k) (ω : Ω[A⁄Λ]) ↦
    r ⊗ₜ[B] map Λ Λ A B ω) (fun _ _ _ ↦ by simp only [add_tmul])
    (fun _ _ _ ↦ by simp only [smul_tmul']) (fun _ _ _ ↦ by simp only [map_add, tmul_add])
    (fun _ _ _ ↦ by simp only [map_smul, tmul_smul])
  TensorProduct.AlgebraTensorModule.lift F

lemma mapRelCotangent_tmul (f : A ⟶ B) (r : k) (ω : Ω[A⁄Λ]) :
    letI := f.relativeAlgebra
    mapRelCotangent f (r ⊗ₜ[A] ω) = r ⊗ₜ[B] map Λ Λ A B ω := rfl

/-- The canonical `k`-linear map from cotangent space to relative cotangent space. -/
def cotangentComplex (A : LocAlgCat.{w} Λ k) : CotangentSpace A →ₗ[k] RelCotangent A where
  toFun x := kerCotangentToTensor Λ A k <| Ideal.Cotangent.equivOfEq (maximalIdeal A)
    (RingHom.ker (algebraMap A k)) (by rw [← ker_residue, ← RingHom.ker_coe_toRingHom, residue,
      IsScalarTower.coe_toAlgHom]) x
  map_add' := by simp
  map_smul' r x := by
    obtain ⟨r, rfl⟩ := A.residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    rw [residue_smul_cotangent, ← map_smul, Ideal.Cotangent.equivOfEq_toCotangent,
      kerCotangentToTensor_toCotangent, RingHom.id_apply, Ideal.Cotangent.equivOfEq_toCotangent,
      kerCotangentToTensor_toCotangent, map_smul, SetLike.val_smul, smul_eq_mul]
    change 1 ⊗ₜ[A] (D Λ A) (r * x.val) = A.residue r • 1 ⊗ₜ[A] (D Λ A) x.val
    rw [Derivation.leibniz, tmul_add, tmul_smul, smul_tmul', Algebra.smul_def,
      ← smul_tmul, Algebra.smul_def, ← residue_toRingHom, RingHom.coe_coe,
      residue_eq_zero_iff.mpr x.prop, zero_mul, zero_tmul, add_zero, smul_tmul', smul_eq_mul]

@[simp]
lemma cotangentComplex_toCotangent (A : LocAlgCat.{w} Λ k) (a : maximalIdeal A) :
    A.cotangentComplex ((maximalIdeal A).toCotangent a) = 1 ⊗ₜ (D Λ A) a := rfl

/-- The canonical extension of `k` associated to the object `A`, defined via
its surjective residue map. -/
abbrev extension (A : LocAlgCat.{w} Λ k) : Extension Λ k :=
  (Extension.ofSurjective A.residue A.residue_surjective)

namespace Extension

@[simp]
lemma residue_σ_apply (A : LocAlgCat.{w} Λ k) (r : k) :
    A.residue (A.extension.σ r) = r := A.extension.algebraMap_σ r

/-- The canonical `Λ`-algebra equivalence between the underlying ring of
the extension associated to `A` and `A` itself. -/
abbrev ringAlgEquiv (A : LocAlgCat.{w} Λ k) : A.extension.Ring ≃ₐ[Λ] A :=
  AlgEquiv.refl

lemma residue_ringAlgEquiv_apply (x : A.extension.Ring) : A.residue (ringAlgEquiv A x) =
    algebraMap A.extension.Ring k x := rfl

lemma ringAlgEquiv_apply_smul (a : A.extension.Ring) (r : k) : ringAlgEquiv A a • r = a • r := by
  rw [Algebra.smul_def, Algebra.smul_def, ← residue_apply, residue_ringAlgEquiv_apply]

/-- The canonical linear equivalence between the module of Kähler differentials of
the extension ring associated to `A` and that of `A`. -/
abbrev kaehlerEquiv (A : LocAlgCat.{w} Λ k) : Ω[A.extension.Ring⁄Λ] ≃ₗ[Λ] Ω[A⁄Λ] :=
  LinearEquiv.refl Λ _

lemma kaehlerEquiv_smul (ω : Ω[A.extension.Ring⁄Λ]) (a : A.extension.Ring) :
    kaehlerEquiv A (a • ω) = ringAlgEquiv A a • kaehlerEquiv A ω := rfl

lemma kaehlerEquiv_symm_smul (ω : Ω[A⁄Λ]) (a : A) :
    (kaehlerEquiv A).symm (a • ω) = (ringAlgEquiv A).symm a • (kaehlerEquiv A).symm ω := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical `k`-linear equivalence between the cotangent space of
the extension associated to `A` and the cotangent space of `A`. -/
def cotangentEquiv (A : LocAlgCat.{w} Λ k) : A.extension.Cotangent ≃ₗ[k] CotangentSpace A where
  toFun x := Ideal.Cotangent.equivOfEq A.extension.ker (maximalIdeal A) A.ker_residue <|
    A.extension.cotangentEquivCotangentKer x
  map_add' := by simp
  map_smul' r x := by
    simp only [Extension.cotangentEquivCotangentKer_apply, Extension.Cotangent.val_smul,
      RingHom.id_apply]
    rcases A.extension.ker.toCotangent_surjective x.val with ⟨y, hy⟩
    nth_rw 2 [← residue_σ_apply A r]
    rw [← hy, residue_smul_cotangent, ← map_smul, Ideal.Cotangent.equivOfEq_toCotangent,
      Ideal.Cotangent.equivOfEq_toCotangent, ← map_smul, Ideal.toCotangent_eq]
    simp
  invFun x := A.extension.cotangentEquivCotangentKer.symm <|
    (Ideal.Cotangent.equivOfEq A.extension.ker (maximalIdeal A) A.ker_residue).symm x
  left_inv _ := by simp only [LinearEquiv.symm_apply_apply]
  right_inv _ := by simp only [LinearEquiv.apply_symm_apply]

@[simp]
lemma cotangentEquiv_mk_apply (A : LocAlgCat.{w} Λ k) (x : A.extension.ker) :
    Extension.cotangentEquiv A (Extension.Cotangent.mk x) =
      (maximalIdeal A).toCotangent ⟨x.val, by rw [← ker_residue]; exact x.prop⟩ := rfl

/-- Implementation details of `cotangentSpaceEquiv`. -/
private def cotangentSpaceEquivAux (A : LocAlgCat.{w} Λ k) :
    k →ₗ[k] Ω[A.extension.Ring⁄Λ] →ₗ[A.extension.Ring] A.RelCotangent := .mk₂' k A.extension.Ring
  (fun (r : k) (ω : Ω[A.extension.Ring⁄Λ]) ↦ r ⊗ₜ[A] kaehlerEquiv A ω)
  (fun _ _ _ ↦ by simp only [add_tmul]) (fun _ _ _ ↦ by simp only [smul_tmul'])
  (fun _ _ _ ↦ by simp only [← tmul_add, ← map_add]) (fun _ _ _ ↦ by
    simp only [kaehlerEquiv_smul, tmul_smul, smul_tmul', ← ringAlgEquiv_apply_smul])

/-- Implementation details of `cotangentSpaceEquiv`. -/
private def cotangentSpaceEquivAux' (A : LocAlgCat.{w} Λ k) :
    k →ₗ[k] Ω[A⁄Λ] →ₗ[A] A.extension.CotangentSpace := .mk₂' k A
  (fun (r : k) (ω : Ω[A⁄Λ]) ↦ r ⊗ₜ[A.extension.Ring] (kaehlerEquiv A).symm ω)
  (fun _ _ _ ↦ by simp only [add_tmul]) (fun _ _ _ ↦ by simp only [smul_tmul'])
  (fun _ _ _ ↦ by simp only [← tmul_add, ← map_add]) (fun a r ω ↦ by
    simp only [kaehlerEquiv_symm_smul, tmul_smul, smul_tmul']
    nth_rw 2 [← (ringAlgEquiv A).apply_symm_apply a]
    rw [ringAlgEquiv_apply_smul])

/-- The canonical linear equivalence between the cotangent space of
the extension associated to `A` and the relative cotangent space of `A`. -/
@[no_expose]
def cotangentSpaceEquiv (A : LocAlgCat.{w} Λ k) :
    A.extension.CotangentSpace ≃ₗ[k] A.RelCotangent := .ofLinear
  (TensorProduct.AlgebraTensorModule.lift (cotangentSpaceEquivAux A))
  (TensorProduct.AlgebraTensorModule.lift (cotangentSpaceEquivAux' A))
  (by ext; simp [cotangentSpaceEquivAux, cotangentSpaceEquivAux'])
  (by ext; simp [cotangentSpaceEquivAux, cotangentSpaceEquivAux'])

@[simp]
lemma cotangentSpaceEquiv_tmul (r : k) (ω : Ω[A.extension.Ring⁄Λ]) :
    cotangentSpaceEquiv A (r ⊗ₜ ω) = r ⊗ₜ (kaehlerEquiv A) ω := by
  simp [cotangentSpaceEquiv, cotangentSpaceEquivAux]

@[simp]
lemma cotangentSpaceEquiv_symm_tmul (r : k) (ω : Ω[A⁄Λ]) :
    (cotangentSpaceEquiv A).symm (r ⊗ₜ ω) = r ⊗ₜ (kaehlerEquiv A).symm ω := by
  simp [cotangentSpaceEquiv, cotangentSpaceEquivAux']

theorem cotangentSpaceEquiv_comp_cotangentComplex :
    (cotangentSpaceEquiv A).toLinearMap.comp A.extension.cotangentComplex =
      A.cotangentComplex.comp (cotangentEquiv A).toLinearMap := LinearMap.ext fun x ↦ by
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  rfl

end Extension

section IsLocalRing

open LinearMap

variable [IsLocalRing Λ] [Algebra.IsIntegral Λ k]

instance : Module (ResidueField Λ) (CotangentSpace A) :=
  fast_instance% .restrictScalars (ResidueField Λ) k (CotangentSpace A)

lemma residueField_smul_cotangent (r : ResidueField Λ)
    (x : CotangentSpace A) : r • x = (algebraMap (ResidueField Λ) k r) • x := rfl

instance : IsScalarTower (ResidueField Λ) k (CotangentSpace A) := .restrictScalars ..

instance : IsScalarTower Λ (ResidueField Λ) (CotangentSpace A) := .of_algebraMap_smul fun _ _ ↦ by
  rw [residueField_smul_cotangent, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]

theorem surjective_mapCotangent_toSpecialFiber : Surjective (mapCotangent A.toSpecialFiber) :=
  surjective_mapCotangent_toOfQuot _

/-- The canonical linear map from the cotangent space of `Λ` to the cotangent space of `A`. -/
def baseCotangentMap (A : LocAlgCat.{w} Λ k) :
    CotangentSpace Λ →ₗ[ResidueField Λ] CotangentSpace A :=
  ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by rw [← Ideal.comap_coe,
    Algebra.toRingHom_ofId, comap_algebraMap_maximalIdeal])).extendScalarsOfSurjective
      IsLocalRing.residue_surjective

@[simp]
lemma baseCotangentMap_toCotangent (x : maximalIdeal Λ) :
    A.baseCotangentMap ((maximalIdeal Λ).toCotangent x) =
      (maximalIdeal A).toCotangent ⟨algebraMap Λ A x, by
        have := isLocalHom_algebraMap A
        rw [← Ideal.mem_comap, maximalIdeal_comap]; exact x.prop⟩ := rfl

theorem range_baseCotangentMap_le (A : LocAlgCat Λ k) :
    A.baseCotangentMap.range ≤ A.cotangentComplex.ker.restrictScalars _ := fun x hx ↦ by
  obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
  rcases hx with ⟨y, hy⟩
  rw [Submodule.restrictScalars_mem, mem_ker, ← hy]
  obtain ⟨y, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective y
  simp

lemma mapCotangent_comp_liftBaseChange_baseCotangentMap (f : A ⟶ B) :
    (mapCotangent f).comp (liftBaseChange k A.baseCotangentMap) =
      liftBaseChange k B.baseCotangentMap := LinearMap.ext fun z ↦ by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rcases (maximalIdeal Λ).toCotangent_surjective a with ⟨a, rfl⟩
    simp
  | add x y hx hy => simp_all

open Submodule in
theorem range_liftBaseChange_baseCotangentMap :
    (liftBaseChange k A.baseCotangentMap).range = (mapCotangent A.toSpecialFiber).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    rcases hx with ⟨y, hy⟩; rw [← hy]
    clear * -; induction y with
    | zero => simp
    | tmul x y =>
      rcases (maximalIdeal Λ).toCotangent_surjective y with ⟨y, rfl⟩
      simp [Ideal.toCotangent_eq_zero]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · rcases (maximalIdeal A).toCotangent_surjective x with ⟨⟨x, x_in⟩, rfl⟩
    simp only [LinearMap.mem_ker, mapCotangent_toCotangent, toAlgHom_toOfQuot_apply,
      Ideal.toCotangent_eq_zero] at hx
    rw [← toAlgHom_toOfQuot_apply, ← map_toAlgHom_toOfQuot_maximalIdeal_eq, ← Ideal.map_pow,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ surjective_toAlgHom_toOfQuot,
      ker_toAlgHom_toOfQuot, mem_sup] at hx
    rcases hx with ⟨u, u_in, v, v_in, huv⟩
    simp_rw [← huv]
    have pow_le : maximalIdeal A ^ 2 ≤ maximalIdeal A := Ideal.pow_le_self (by simp)
    have : IsLocalHom (algebraMap Λ A) := isLocalHom_algebraMap A
    rw [← AddMemClass.mk_add_mk _ u v (pow_le u_in) (map_maximalIdeal_le _ v_in), map_add,
      (Ideal.toCotangent_eq_zero ..).mpr ‹_›, zero_add]
    clear * -; rw [Ideal.map, Ideal.span] at v_in
    induction v_in using span_induction with
    | mem _ hx =>
      obtain ⟨x, x_in, rfl⟩ := hx
      exact ⟨1 ⊗ₜ (maximalIdeal Λ).toCotangent ⟨x, x_in⟩, by simp⟩
    | zero => simp [(mk_eq_zero ..).mpr]
    | add z w hz hw ihz ihw =>
      simpa only [← AddMemClass.mk_add_mk _ z w (map_maximalIdeal_le _ hz)
        (map_maximalIdeal_le _ hw)] using add_mem (ihz hz) (ihw hw)
    | smul a x hx ihx =>
      simpa only [← SetLike.mk_smul_mk _ _ _ (map_maximalIdeal_le _ hx), map_smul,
        ← residue_smul_cotangent] using smul_mem _ _ (ihx hx)

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
  rw [← B.range_liftBaseChange_baseCotangentMap, LinearMap.mem_range] at h_ker
  rcases h_ker with ⟨z, hz⟩
  use x + liftBaseChange k A.baseCotangentMap z
  rw [map_add, ← LinearMap.comp_apply, mapCotangent_comp_liftBaseChange_baseCotangentMap, hz,
    add_sub_cancel]

end IsLocalRing

end LocAlgCat
