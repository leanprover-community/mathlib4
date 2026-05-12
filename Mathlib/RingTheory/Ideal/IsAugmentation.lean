/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Projection
public import Mathlib.RingTheory.Ideal.Maps

/-! # Augmentation ideals

## Main definitions

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if its underlying submodule is a complement of `1 : Submodule A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

## Main results

* `Ideal.isAugmentation_baseChange`: if `R` is a `CommRing` and an `A`-algebra,
then the ideal `R ⊗[A] I` of `R ⊗[A] S` is an augmentation ideal.

## Notes

* There is a weaker version that holds for general commutative rings and would just assert that the
  quotient map `R →+* R ⧸ I` has a section which is a ring homomorphism (possibly with a variant
  “with data” that keeps track of the choice of one such section).

-/

@[expose] public section

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*}

open Submodule Subalgebra

/-- An ideal `I` of an `R`-algebra `A` is an augmentation ideal
if its underlying module is a complement to `1 : Submodule R A`. -/
def IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop :=
  IsCompl 1 (I.restrictScalars R)

lemma isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) :
    I.IsAugmentation R ↔ IsCompl 1 (I.restrictScalars R) := Iff.rfl

/-- If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augmentation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure. -/
theorem isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A]
    {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictScalars R) := by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

end Ideal

end

namespace Submodule

/- This section proves the complementary property for tensor products that is necessary to prove
  that the tensor product of algebras with augmentation ideals has an augmentation ideal -/
open TensorProduct LinearMap

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {M' M'' : Submodule A M}
  {N : Type*} [AddCommGroup N] [Module A N] {N' N'' : Submodule A N}

variable (M' N') in
/-- The submodule of M ⊗[A] N image of M' ⊗[A] N' -/
noncomputable def TensorProduct : Submodule A (M ⊗[A] N) :=
  (TensorProduct.mapIncl M' N').range

namespace TensorProduct

variable (A M N) in
theorem top_top : TensorProduct (⊤ : Submodule A M) (⊤ : Submodule A N) = ⊤ := by
  simp [ -mapIncl, TensorProduct, range_mapIncl, map₂_mk_top_top_eq_top, ← span_tmul_eq_top]

variable (N') in
lemma mono_left (h : M' ≤ M'') : TensorProduct M' N' ≤ TensorProduct M'' N' :=
  TensorProduct.range_mapIncl_mono  h le_rfl

variable (M') in
lemma mono_right (h : N' ≤ N'') : TensorProduct M' N' ≤ TensorProduct M' N'' :=
  TensorProduct.range_mapIncl_mono le_rfl h

variable (N') in
lemma sup_left : TensorProduct (M' ⊔ M'') N' = TensorProduct M' N' ⊔ TensorProduct M'' N' := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, zero_mem]
    | tmul m n =>
      rcases m with ⟨_, hm⟩
      rcases mem_sup.mp hm with ⟨m', hm', m'', hm'', rfl⟩
      simp only [mapIncl, map_tmul, coe_subtype, add_tmul]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · exact ⟨⟨m', hm'⟩ ⊗ₜ[A] n, rfl⟩
      · exact ⟨⟨m'', hm''⟩ ⊗ₜ[A] n, rfl⟩
    | add x y hx hy => simp only [map_add, add_mem hx hy]
  · simp only [sup_le_iff]
    refine ⟨range_mapIncl_mono le_sup_left le_rfl,
      range_mapIncl_mono le_sup_right le_rfl⟩

variable (M') in
lemma sup_right : TensorProduct M' (N' ⊔ N'') = TensorProduct M' N' ⊔ TensorProduct M' N'' := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, zero_mem]
    | tmul m n =>
      rcases n with ⟨_, hn⟩
      rcases mem_sup.mp hn with ⟨n', hn', n'', hn'', rfl⟩
      simp only [mapIncl, map_tmul, coe_subtype, tmul_add]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · exact ⟨m ⊗ₜ[A] ⟨n', hn'⟩, rfl⟩
      · exact ⟨m ⊗ₜ[A] ⟨n'', hn''⟩, rfl⟩
    | add x y hx hy => simp only [map_add, add_mem hx hy]
  · simp only [sup_le_iff]
    refine ⟨range_mapIncl_mono le_rfl le_sup_left,
      range_mapIncl_mono le_rfl le_sup_right⟩

variable (N') in
lemma disjoint_left (hM : IsCompl M' M'') :
    Disjoint (TensorProduct M' N') (TensorProduct M'' N') := by
  have hq : M'.subtype.comp (projectionOnto _ _ hM) +
      M''.subtype.comp (projectionOnto _ _ hM.symm) = LinearMap.id := by
    ext x
    simp only [add_apply, coe_comp, coe_subtype, Function.comp_apply, id_coe, id_eq]
    erw [projection_add_projection_eq_self]
  rw [disjoint_def]
  intro x h h'
  rw [← id_apply x (R := A), ← rTensor_id, ← hq]
  simp only [rTensor_add, rTensor_comp, add_apply, coe_comp, Function.comp_apply]
  change x ∈ (TensorProduct.map _ N'.subtype).range at h h'
  rw [← rTensor_comp_lTensor] at h h'
  replace h : x ∈ (LinearMap.rTensor N M'.subtype).range :=
    range_comp_le_range _ _ h
  replace h' : x ∈ (LinearMap.rTensor N M''.subtype).range :=
    range_comp_le_range _ _ h'
  rw [← ker_rTensor_projectionOnto hM.symm N, mem_ker] at h
  rw [← ker_rTensor_projectionOnto hM N, mem_ker] at h'
  simp only [h, h', _root_.map_zero, add_zero]

variable (M') in
lemma disjoint_right {N' N'' : Submodule A N} (hN : IsCompl N' N'') :
    Disjoint (TensorProduct M' N') (TensorProduct M' N'') := by
  have hq : N'.subtype.comp (projectionOnto _ _ hN) +
      N''.subtype.comp (projectionOnto _ _ hN.symm) = LinearMap.id := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.coe_comp, coe_subtype, Function.comp_apply,
      LinearMap.id_coe, id_eq]
    erw [projection_add_projection_eq_self]
  rw [disjoint_def]
  intro x h h'
  rw [← LinearMap.id_apply x (R := A), ← LinearMap.lTensor_id, ← hq]
  simp only [LinearMap.lTensor_add, LinearMap.lTensor_comp, LinearMap.add_apply,
    LinearMap.coe_comp, Function.comp_apply]
  change x ∈ LinearMap.range (TensorProduct.map M'.subtype _) at h h'
  rw [← LinearMap.lTensor_comp_rTensor] at h h'
  replace h : x ∈ LinearMap.range (LinearMap.lTensor M N'.subtype) :=
    LinearMap.range_comp_le_range _ _ h
  replace h' : x ∈ LinearMap.range (LinearMap.lTensor M N''.subtype) :=
    LinearMap.range_comp_le_range _ _ h'
  rw [← ker_lTensor_projectionOnto hN.symm M, LinearMap.mem_ker] at h
  rw [← ker_lTensor_projectionOnto hN M, LinearMap.mem_ker] at h'
  simp only [h, h', _root_.map_zero, add_zero]

variable (N) in
theorem isCompl_left_top (hM : IsCompl M' M'') :
    IsCompl (TensorProduct M' (⊤ : Submodule A N)) (TensorProduct M'' ⊤) := by
  apply IsCompl.mk
  · exact disjoint_left ⊤ hM
  · rw [codisjoint_iff, ← sup_left, codisjoint_iff.mp hM.codisjoint]
    exact top_top A M N

variable (M) in
theorem isCompl_right_top {N' N'' : Submodule A N} (hN : IsCompl N' N'') :
    IsCompl (TensorProduct (⊤ : Submodule A M) N') (TensorProduct ⊤ N'') := by
  apply IsCompl.mk
  · exact disjoint_right ⊤ hN
  · rw [codisjoint_iff, ← sup_right, codisjoint_iff.mp hN.codisjoint]
    exact top_top A M N

theorem isCompl_left_left (hM : IsCompl M' M'') (hN : IsCompl N' N'') :
    IsCompl (TensorProduct M' N') (TensorProduct ⊤ N'' ⊔ TensorProduct M'' ⊤) := by
  suffices TensorProduct M' N'' ⊔ TensorProduct M'' ⊤
    = TensorProduct ⊤ N'' ⊔ M''.TensorProduct ⊤ by
    rw [← this]
    apply Submodule.isCompl_assoc_of_disjoint_left
    · exact disjoint_right M' hN
    · rw [← sup_right, codisjoint_iff.mp hN.codisjoint]
      exact isCompl_left_top N hM
  rw [← codisjoint_iff.mp hM.codisjoint, sup_left, ← codisjoint_iff.mp hN.codisjoint, sup_right]
  simp only [sup_assoc]
  apply congr_arg₂ _ rfl
  nth_rewrite 3 [sup_comm]
  rw [← sup_assoc, sup_idem, sup_comm]

end Submodule.TensorProduct

section Augmentation

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra A R] (J : Ideal A)

open TensorProduct Ideal LinearMap Submodule

/-- If `I` is an augmentation ideal of the `A`-algebra `R` and `R` is an `A`-algebra,
then the ideal `R ⊗[A] I` of `R ⊗[A] S` is an augmentation ideal. -/
theorem isAugmentation_baseChange
    {A : Type*} [CommRing A]
    {S : Type*} [Ring S] [Algebra A S]
    {I : Ideal S} (hI : IsAugmentation A I)
    {R : Type*} [CommRing R] [Algebra A R] :
    (Ideal.map Algebra.TensorProduct.includeRight I : Ideal (R ⊗[A] S)).IsAugmentation R := by
  rw [isAugmentation_iff, Algebra.TensorProduct.map_includeRight_eq_range_baseChange,
    Algebra.baseChange_one]
  exact isCompl_baseChange hI R

theorem _root_.Algebra.TensorProduct.map_toLinearMap (A : Type*) [CommSemiring A]
    {R R₀ S S₀ : Type*} [Semiring R] [Semiring R₀] [Semiring S] [Semiring S₀]
    [Algebra A R] [Algebra A R₀] [Algebra A S] [Algebra A S₀] (f : R₀ →ₐ[A] R) (g : S₀ →ₐ[A] S) :
    (Algebra.TensorProduct.map f g).toLinearMap =
      (TensorProduct.map f.toLinearMap g.toLinearMap) := by
  rw [Algebra.TensorProduct.toLinearMap_map, AlgebraTensorModule.map_eq]

theorem AlgHom.toLinearMap_eq_coe {A R₀ R : Type*} [CommSemiring A] [Semiring R₀] [Semiring R]
    [Algebra A R] [Algebra A R₀] (f : R₀ →ₐ[A] R) :
    f.toLinearMap = f := by
  exact LinearMap.ext (congrFun rfl)

theorem _root_.Algebra.TensorProduct.coe_map (A : Type*) [CommSemiring A]
    {R R₀ S S₀ : Type*} [Semiring R] [Semiring R₀] [Semiring S] [Semiring S₀]
    [Algebra A R] [Algebra A R₀] [Algebra A S] [Algebra A S₀] (f : R₀ →ₐ[A] R) (g : S₀ →ₐ[A] S) :
    (Algebra.TensorProduct.map f g : R₀ ⊗[A] S₀ →ₗ[A] R ⊗[A] S) =
      TensorProduct.map f g := by
  rw [← DFunLike.coe_fn_eq, coe_coe, ← AlgHom.coe_toLinearMap,
    Algebra.TensorProduct.map_toLinearMap]
  simp [AlgHom.toLinearMap_eq_coe]

theorem _root_.Algebra.TensorProduct.map_range_toSubmodule
    (A : Type*) [CommSemiring A]
    {R R₀ S S₀ : Type*} [Semiring R] [Semiring R₀] [Semiring S] [Semiring S₀]
    [Algebra A R] [Algebra A R₀] [Algebra A S] [Algebra A S₀]
    (f : R₀ →ₐ[A] R) (g : S₀ →ₐ[A] S) :
    Subalgebra.toSubmodule (Algebra.TensorProduct.map f g).range =
      (TensorProduct.map f.toLinearMap g.toLinearMap).range := by
  rw [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range, ← AlgHom.coe_toLinearMap,
    ← LinearMap.coe_range, Algebra.TensorProduct.toLinearMap_map, AlgebraTensorModule.map_eq]

theorem _root_.Subalgebra.val_toLinearMap (A : Type*) [CommSemiring A] {R : Type*} [Semiring R]
    [Algebra A R] {R₀ : Subalgebra A R} :
    R₀.val.toLinearMap = R₀.toSubmodule.subtype := by
  rfl

theorem isAugmentation_tensorProduct (A : Type*) [CommRing A] {R S : Type*} [CommRing R]
    [Algebra A R] {R₀ : Subalgebra A R} {I : Ideal R} (hI : I.IsAugmentation R₀) [CommRing S]
    [Algebra A S] {S₀ : Subalgebra A S} {J : Ideal S} (hJ : J.IsAugmentation S₀) :
    let K : Ideal (R ⊗[A] S) := I.map (Algebra.TensorProduct.includeLeft (S := A)) ⊔
      J.map Algebra.TensorProduct.includeRight
    let T₀ : Subalgebra A (R ⊗[A] S) := Subalgebra.map (Algebra.TensorProduct.map R₀.val S₀.val) ⊤
    K.IsAugmentation T₀ := by
  rw [Ideal.isAugmentation_subalgebra_iff] at hI hJ ⊢
  convert Submodule.TensorProduct.isCompl_left_left hI hJ
  · simp only [Submodule.TensorProduct, Algebra.map_top, mapIncl]
    rw [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range,
      ← AlgHom.coe_toLinearMap, ← LinearMap.coe_range,
        Algebra.TensorProduct.toLinearMap_map, AlgebraTensorModule.map_eq]
    simp [Subalgebra.val_toLinearMap]
  · simp only [restrictScalars_sup, Submodule.TensorProduct, mapIncl]
    have : (I.map (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S)).restrictScalars A =
        (TensorProduct.map (I.restrictScalars A).subtype (⊤ : Submodule A S).subtype).range := by
      rw [Ideal.map_includeLeft_eq, rTensor_def]
      rw [← id_comp (⊤: Submodule A S).subtype, ← comp_id (Submodule.restrictScalars A
      I).subtype, TensorProduct.map_comp, range_comp, comp_id, LinearMap.range_eq_map]
      congr
      rw [eq_comm, range_eq_top]
      apply TensorProduct.map_surjective Function.surjective_id
      rw [← LinearMap.range_eq_top, range_subtype]
    rw [sup_comm, this]
    have : (J.map (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S)).restrictScalars A =
        (TensorProduct.map (⊤ : Submodule A R).subtype (J.restrictScalars  A).subtype).range := by
      rw [Ideal.map_includeRight_eq, lTensor_def]
      rw [← id_comp (⊤: Submodule A R).subtype, ← comp_id (Submodule.restrictScalars A
      J).subtype, TensorProduct.map_comp, range_comp, comp_id, LinearMap.range_eq_map]
      congr
      rw [eq_comm, range_eq_top]
      apply TensorProduct.map_surjective _ Function.surjective_id
      rw [← LinearMap.range_eq_top, range_subtype]
    rw [this]

end Ideal

end Augmentation
