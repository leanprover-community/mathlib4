/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Set.Pointwise.SMul

/-!
# Pointwise actions of linear maps
-/

open Pointwise

variable {R S : Type*} (M M₁ M₂ N : Type*)
variable [Semiring R] [Semiring S] (σ : R →+* S)
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module S N]
variable {F : Type*} (h : F)

-- @[simp] Not longer applies to itself #8386
theorem image_smul_setₛₗ [FunLike F M N] [SemilinearMapClass F σ M N] (c : R) (s : Set M) :
    h '' (c • s) = σ c • h '' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨z, zs, rfl⟩, rfl⟩
    exact ⟨h z, Set.mem_image_of_mem _ zs, (map_smulₛₗ _ _ _).symm⟩
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (Set.mem_image _ _ _).2 ⟨c • z, Set.smul_mem_smul_set hz, map_smulₛₗ _ _ _⟩
#align image_smul_setₛₗ image_smul_setₛₗ

theorem preimage_smul_setₛₗ [FunLike F M N] [SemilinearMapClass F σ M N] {c : R} (hc : IsUnit c)
    (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ys, hy⟩
    refine' ⟨(hc.unit.inv : R) • x, _, _⟩
    · simp only [← hy, smul_smul, Set.mem_preimage, Units.inv_eq_val_inv, map_smulₛₗ h, ← map_mul,
        IsUnit.val_inv_mul, one_smul, map_one, ys]
    · simp only [smul_smul, IsUnit.mul_val_inv, one_smul, Units.inv_eq_val_inv]
  · rintro x ⟨y, hy, rfl⟩
    refine' ⟨h y, hy, by simp only [RingHom.id_apply, map_smulₛₗ h]⟩
#align preimage_smul_setₛₗ preimage_smul_setₛₗ

variable (R)

theorem image_smul_set [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂] (c : R) (s : Set M₁) :
    h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s
#align image_smul_set image_smul_set

theorem preimage_smul_set [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂]
    {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s := preimage_smul_setₛₗ _ _ _ h hc s
#align preimage_smul_set preimage_smul_set
