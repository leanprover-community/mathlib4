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

open Set Pointwise

variable {R S : Type*} (M M₁ M₂ N : Type*)
variable [Monoid R] [Monoid S]
variable {G : Type*} (σ : G)
-- variable [Semiring R] [Semiring S] (σ : R →+* S)
-- variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N]
-- variable [Module R M] [Module R M₁] [Module R M₂] [Module S N]
variable [MulAction R M] [MulAction S N] [MulAction R M₁] [MulAction R M₂]
variable {F : Type*} (h : F)

-- @[simp] -- In #8386, the `simp_nf` linter complains:
-- "Left-hand side does not simplify, when using the simp lemma on itself."
-- For now we will have to manually add `image_smul_setₛₗ _` to the `simp` argument list.
-- TODO: when lean4#3107 is fixed, mark this as `@[simp]`.
theorem image_smul_setₛₗ
    [FunLike G R S] [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set M) :
    h '' (c • s) = σ c • h '' s := by
  simp only [← image_smul, image_image, map_smulₛₗ h]
#align image_smul_setₛₗ image_smul_setₛₗ

theorem preimage_smul_setₛₗ
    [FunLike G R S] [MonoidHomClass G R S] [FunLike F M N] [MulActionSemiHomClass F σ M N]
    {c : R} (hc : IsUnit c) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  lift c to Rˣ using hc
  calc h ⁻¹' ((Units.map (σ : R →* S) c) • s)
      = (σ (c⁻¹).1 • h ·) ⁻¹' s := by rw [← preimage_smul_inv]; rfl
    _ = c • h ⁻¹' s := by simp only [← map_smulₛₗ h, ← preimage_smul_inv]; rfl
#align preimage_smul_setₛₗ preimage_smul_setₛₗ

variable (R)

@[simp] -- This can be safely removed as a `@[simp]` lemma if `image_smul_setₛₗ` is readded.
theorem image_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₁) :
    h '' (c • s) = c • h '' s :=
  -- ACL: was exact @image_smul_setₛₗ _ _ _ h c s
  image_smul_setₛₗ _ _ (MonoidHom.id R) h c s
#align image_smul_set image_smul_set

/-- Translation of preimage is contained in preimage of translation -/
theorem preimage_smul_setₑ_le
    [FunLike G R S] [FunLike F M N] [MulActionSemiHomClass F σ M N]
    {c : R} (t : Set N) :
    c • h ⁻¹' t ⊆ h ⁻¹' (σ c • t) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨h y, hy, (by rw [map_smulₛₗ])⟩

theorem preimage_smul_set_le
    [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    {c : R} (t : Set M₂) : c • h ⁻¹' t ⊆ h ⁻¹' (c • t) :=
  preimage_smul_setₑ_le _ _ _ (MonoidHom.id R) h t

theorem preimage_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  -- ACL: was preimage_smul_setₛₗ _ _ _ h hc s
  preimage_smul_setₛₗ _ _ (MonoidHom.id R) h hc s
#align preimage_smul_set preimage_smul_set
