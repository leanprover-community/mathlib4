/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!

# Lemmas about tensor products of central algebras

In this file we prove for algebras `B` and `C` over a field `K` that if `B ⊗[K] C` is a central
algebra and `B, C` nontrivial, then both `B` and `C` are central algebras.

## Main Results

- `Algebra.IsCentral.left_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `C` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.
- `Algebra.IsCentral.right_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `C` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.

## Tags
Central Algebras, Central Simple Algebras, Noncommutative Algebra
-/

universe u v

open TensorProduct

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

lemma Algebra.TensorProduct.includeLeft_map_center_le :
    (Subalgebra.center K B).map includeLeft ≤ Subalgebra.center K (B ⊗[K] C) := by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

lemma Algebra.TensorProduct.includeRight_map_center_le :
    (Subalgebra.center K C).map includeRight ≤ Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

lemma Algebra.TensorProduct.left_tensor_base_sup_base_tensor_right
    (K B C : Type*) [CommRing K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (map (AlgHom.id K B) (Algebra.ofId K C)).range ⊔
    (map (Algebra.ofId K B) (AlgHom.id K C)).range = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | tmul b c =>
    rw [show b ⊗ₜ[K] c = b ⊗ₜ[K] 1 * 1 ⊗ₜ[K] c by simp]
    exact Algebra.mul_mem_sup ⟨b ⊗ₜ 1, by simp⟩ ⟨1 ⊗ₜ c, by simp⟩
  | add x y hx hy =>
    exact Subalgebra.add_mem _ hx hy

lemma TensorProduct.submodule_tensor_inf_tensor_submodule
    (K B C : Type u) [Field K] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    LinearMap.range (map b.subtype .id) ⊓
    LinearMap.range (map .id c.subtype) =
    LinearMap.range (map b.subtype c.subtype) := by

  refine le_antisymm ?_ ?_
  · let u : b ⊗[K] c →ₗ[K] B ⊗[K] c := map b.subtype LinearMap.id
    let v : B ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] c := map (Submodule.mkQ _) LinearMap.id
    have exactuv : Function.Exact u v := by
      apply rTensor_exact
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
      exact Submodule.mkQ_surjective _

    let u' : b ⊗[K] C →ₗ[K] B ⊗[K] C := map b.subtype LinearMap.id
    let v' : B ⊗[K] C →ₗ[K] (B ⧸ b) ⊗[K] C := map (Submodule.mkQ _) LinearMap.id
    have exactu'v' : Function.Exact u' v' := by
      apply rTensor_exact
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
      exact Submodule.mkQ_surjective _

    let α : b ⊗[K] c →ₗ[K] b ⊗[K] C := map LinearMap.id c.subtype
    let β : B ⊗[K] c →ₗ[K] B ⊗[K] C := map LinearMap.id c.subtype
    let γ : (B ⧸ b) ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] C := map LinearMap.id c.subtype
    have γ_inj : Function.Injective γ :=
      Module.Flat.iff_lTensor_preserves_injective_linearMap (R := K) (M := B ⧸ b)|>.1 inferInstance
        c.subtype c.injective_subtype

    rintro z (hz : z ∈ LinearMap.range u' ⊓ LinearMap.range β)
    obtain ⟨z, rfl⟩ := hz.2
    have comm0 : v' ∘ₗ β = γ ∘ₗ v := by
      ext
      simp [v', β, γ, v]
    have hz1 : v' (β z) = γ (v z) := congr($comm0 z)
    have hz2 : v' (β z) = 0 := by
      rw [← LinearMap.mem_ker]
      rw [LinearMap.exact_iff] at exactu'v'
      rw [exactu'v']
      exact hz.1
    rw [hz2] at hz1
    have hz3 : v z ∈ LinearMap.ker γ := by rw [LinearMap.mem_ker]; exact hz1.symm
    replace hz3 : v z = 0 := by
      rw [← LinearMap.ker_eq_bot] at γ_inj; rw [γ_inj] at hz3; exact hz3
    replace hz3 : z ∈ LinearMap.ker v := hz3
    replace hz3 : z ∈ LinearMap.range u := by
      rw [LinearMap.exact_iff] at exactuv
      rwa [← exactuv]
    obtain ⟨z, rfl⟩ := hz3
    change (β ∘ₗ u) z ∈ _

    have comm1 : β ∘ₗ u = u' ∘ₗ α := by
      ext
      simp [β, u, u', α]

    rw [comm1, LinearMap.comp_apply]
    refine ⟨z, ?_⟩
    simp only [u', α]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨map LinearMap.id c.subtype x, ?_⟩,
      ⟨map b.subtype LinearMap.id x, ?_⟩⟩
    · rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl
    · rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl

-- We need to restrict the universe, because we used properties of flatness.
lemma Algebra.center_tensorProduct
    (K B C : Type u) [Field K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by
  rw [show Subalgebra.center K (B ⊗[K] C) = Subalgebra.centralizer K (⊤ : Subalgebra K (B ⊗[K] C))
    by simp, ← Algebra.TensorProduct.left_tensor_base_sup_base_tensor_right K B C,
    Subalgebra.centralizer_coe_sup,
    Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_left,
    Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_right]
  apply_fun Subalgebra.toSubmodule using Subalgebra.toSubmodule_injective
  simp only [Algebra.inf_toSubmodule, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
      AlgHom.mem_range]
  change LinearMap.range (_root_.TensorProduct.map _ (LinearMap.id)) ⊓
    LinearMap.range (_root_.TensorProduct.map (LinearMap.id) _) =
    LinearMap.range (_root_.TensorProduct.map _ _)
  erw [TensorProduct.submodule_tensor_inf_tensor_submodule K B C
    (Subalgebra.toSubmodule <| .center K B)
    (Subalgebra.toSubmodule <| .center K C)]
  rfl

lemma centerTensorCenter_injective (K : Type u) (B C : Type v) [Field K]
    [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Function.Injective (TensorProduct.map (Subalgebra.center K B).val.toLinearMap
      (Subalgebra.center K C).val.toLinearMap) := by
  have : TensorProduct.map (Subalgebra.val _).toLinearMap (Subalgebra.val _).toLinearMap =
    ((Subalgebra.center K B).val.toLinearMap.rTensor _) ∘ₗ
    ((Subalgebra.center K C).val.toLinearMap.lTensor _) := by
    ext; simp
  rw [this]
  exact Function.Injective.comp (g := (Subalgebra.center K B).val.toLinearMap.rTensor _)
   (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
   (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

-- set_option maxHeartbeats 1200000 in
noncomputable def centerTensor
    (K B C : Type u) [Field K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K B ⊗[K] Subalgebra.center K C ≃ₗ[K]
    Subalgebra.center K (B ⊗[K] C) :=
    (LinearEquiv.ofInjective (TensorProduct.map (Subalgebra.center K B).val.toLinearMap
      (Subalgebra.center K C).val.toLinearMap) (centerTensorCenter_injective K B C)) ≪≫ₗ
    (show _ ≃ₗ[K] Subalgebra.toSubmodule (Subalgebra.center K (B ⊗[K] C)) from LinearEquiv.ofLinear
      (Submodule.inclusion (by
        rw [Algebra.center_tensorProduct K B C]
        intro x hx
        simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩))
      (Submodule.inclusion (by
        intro x hx
        simp only [Subalgebra.mem_toSubmodule, LinearMap.mem_range] at hx ⊢
        rw [Algebra.center_tensorProduct] at hx
        simp only [AlgHom.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩)) rfl rfl)

set_option synthInstance.maxHeartbeats 40000 in
instance TensorProduct.isCentral
    (K A B : Type u) [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A] [isCentral_B : Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) := by
  constructor
  intro _ H
  obtain ⟨x, rfl⟩ := le_of_eq (Algebra.center_tensorProduct K A B) H; clear H
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨a', ha⟩ := isCentral_A.1 a.2
    obtain ⟨b', hb⟩ := isCentral_B.1 b.2
    refine ⟨b' * a', ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, map_mul, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, ← ha, ← hb]
    rw [Algebra.ofId_apply, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [LinearMap.mul_apply', one_mul, mul_one]
    rw [← Algebra.ofId_apply, ← Algebra.ofId_apply]
  | add x y hx hy =>
    obtain ⟨kx, hx⟩ := hx
    obtain ⟨ky, hy⟩ := hy
    refine ⟨kx + ky, ?_⟩
    rw [map_add, hx, hy, map_add]
namespace Algebra.IsCentral

open Algebra.TensorProduct in
lemma left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ ↦ ⟨k, includeLeft_injective (S := K) inj hk⟩

lemma right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K C :=
  have : IsCentral K (C ⊗[K] B) := IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

/-- Let `B` and `C` be two algebras over a field `K`, if `B ⊗[K] C` is central and `C` is
  non-trivial, then `B` is central. -/
lemma left_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial C]
    [Algebra K B] [Algebra K C] [IsCentral K (B ⊗[K] C)] : IsCentral K B :=
  left_of_tensor K B C <| FaithfulSMul.algebraMap_injective K C

/-- Let `B` and `C` be two algebras over a field `K`, if `B ⊗[K] C` is central and `A` is
  non-trivial, then `B` is central. -/
lemma right_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
    [Algebra K B] [Algebra K C] [IsCentral K (B ⊗[K] C)] : IsCentral K C :=
  right_of_tensor K B C <| FaithfulSMul.algebraMap_injective K B


end Algebra.IsCentral
