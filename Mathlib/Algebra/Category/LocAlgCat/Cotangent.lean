/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.AdicCompletion.Functoriality

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

* `LocAlgCat.baseCotangentMap`: The canonical `k`-linear map from the base-changed cotangent space
  of the base ring `Λ` to the cotangent space of `A`.

* `LocAlgCat.exact_baseCotangentMap_mapCotangent_toSpecialFiber`: The exactness of
  the conormal sequence for the special fiber.

-/

@[expose] public section

noncomputable section

universe w v u

open IsLocalRing Function TensorProduct CategoryTheory

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

section IsLocalRing

variable [IsLocalRing Λ]

instance [Algebra.IsIntegral Λ k] : Module (ResidueField Λ) (CotangentSpace A) :=
  fast_instance% .restrictScalars (ResidueField Λ) k (CotangentSpace A)

lemma residueField_smul_cotangent [Algebra.IsIntegral Λ k] (r : ResidueField Λ)
    (x : CotangentSpace A) : r • x = (algebraMap (ResidueField Λ) k r) • x := rfl

instance [Algebra.IsIntegral Λ k] : IsScalarTower (ResidueField Λ) k (CotangentSpace A) :=
  .restrictScalars ..

instance [Algebra.IsIntegral Λ k] : IsScalarTower Λ (ResidueField Λ) (CotangentSpace A) :=
  .of_algebraMap_smul fun _ _ ↦ by rw [residueField_smul_cotangent,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]

theorem surjective_mapCotangent_toSpecialFiber [Algebra.IsIntegral Λ k] :
    Surjective (mapCotangent A.toSpecialFiber) := surjective_mapCotangent_toOfQuot _

/-- The canonical `k`-linear map from the base-changed cotangent space of `Λ`
to the cotangent space of `A`, induced by the algebra structure map. -/
def baseCotangentMap [Algebra.IsIntegral Λ k] (A : LocAlgCat.{w} Λ k) :
    k ⊗[ResidueField Λ] CotangentSpace Λ →ₗ[k] CotangentSpace A :=
  letI baseMap : CotangentSpace Λ →ₗ[ResidueField Λ] CotangentSpace A :=
    ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by rw [← Ideal.comap_coe,
      Algebra.toRingHom_ofId, comap_algebraMap_maximalIdeal])).extendScalarsOfSurjective
    IsLocalRing.residue_surjective
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

@[simp]
lemma baseCotangentMap_tmul [Algebra.IsIntegral Λ k] (r : k) (a : CotangentSpace Λ) :
    A.baseCotangentMap (r ⊗ₜ a) = r • ((maximalIdeal Λ).mapCotangent (maximalIdeal A)
      (Algebra.ofId Λ A) (by rw [← Ideal.comap_coe, Algebra.toRingHom_ofId,
        comap_algebraMap_maximalIdeal]) a) := rfl

@[simp]
lemma mapCotangent_baseCotangentMap_apply [Algebra.IsIntegral Λ k] (f : A ⟶ B)
    (z : k ⊗[ResidueField Λ] CotangentSpace Λ) :
    mapCotangent f (A.baseCotangentMap z) = B.baseCotangentMap z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rcases (maximalIdeal Λ).toCotangent_surjective a with ⟨a, rfl⟩
    simp
  | add x y hx hy => simp [hx, hy]

open Submodule in
theorem range_baseCotangentMap [Algebra.IsIntegral Λ k] :
    A.baseCotangentMap.range = (mapCotangent A.toSpecialFiber).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
    rcases hx with ⟨y, hy⟩
    rw [← hy]; clear * -
    induction y with
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

theorem exact_baseCotangentMap_mapCotangent_toSpecialFiber [Algebra.IsIntegral Λ k] :
    Exact A.baseCotangentMap (mapCotangent A.toSpecialFiber) :=
  LinearMap.exact_iff.mpr A.range_baseCotangentMap.symm

@[stacks 06S3 "(3) => (2)"]
theorem surjective_mapCotangent_of_surjective_mapCotangent_mapSpecialFiber [Algebra.IsIntegral Λ k]
    (f : A ⟶ B) (h : Surjective (mapCotangent (mapSpecialFiber f))) :
    Surjective (mapCotangent f) := by
  intro y
  obtain ⟨x, hx⟩ := h (mapCotangent B.toSpecialFiber y)
  obtain ⟨x, rfl⟩ := surjective_mapCotangent_toSpecialFiber x
  rw [← LinearMap.comp_apply, ← mapCotangent_comp, toOfQuot_comp_mapOfQuot,
    mapCotangent_comp, LinearMap.comp_apply] at hx
  have h_ker : y - mapCotangent f x ∈ LinearMap.ker (mapCotangent B.toSpecialFiber) := by
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  rw [← B.range_baseCotangentMap, LinearMap.mem_range] at h_ker
  rcases h_ker with ⟨z, hz⟩
  exact ⟨x + A.baseCotangentMap z, by simp [hz]⟩

end IsLocalRing

end LocAlgCat
