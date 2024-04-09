/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth, Antoine Chambert-Loir
-/

import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Pointwise actions of equivariant maps

- `image_smul_setₛₗ` and `image_smul_setₛₗ` : under a `σ`-equivariant map,
one has `h '' (c • s) = (σ c) • h '' s`.

- `preimage_smul_setₛₗ`, `preimage_smul_setₛₗ`, `preimage_smul_set` :
one has `h ⁻¹' (σ c • s) = c • h⁻¹' s`

-/

open Set Pointwise

variable {R S : Type*} (M M₁ M₂ N : Type*)

section Monoid

variable [Monoid R] [Monoid S]
variable {G : Type*} (σ : G)
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

/-- Translation of preimage is contained in preimage of translation -/
theorem smul_preimage_set_leₛₗ
    [FunLike G R S] [FunLike F M N] [MulActionSemiHomClass F σ M N]
    {c : R} (t : Set N) :
    c • h ⁻¹' t ⊆ h ⁻¹' (σ c • t) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨h y, hy, (by rw [map_smulₛₗ])⟩

variable (R)

-- Bug : It should be possible to fill in `@id R`

@[simp] -- This can be safely removed as a `@[simp]` lemma if `image_smul_setₛₗ` is readded.
theorem image_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₁) :
    h '' (c • s) = c • h '' s :=
  -- ACL: was exact @image_smul_setₛₗ _ _ _ h c s
  image_smul_setₛₗ _ _ (MonoidHom.id R) h c s
#align image_smul_set image_smul_set

theorem smul_preimage_set_le
    [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    {c : R} (t : Set M₂) :
    c • h ⁻¹' t ⊆ h ⁻¹' (c • t) :=
  smul_preimage_set_leₛₗ _ _ (MonoidHom.id R) h t

theorem preimage_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  -- ACL: was preimage_smul_setₛₗ _ _ _ h hc s
  preimage_smul_setₛₗ _ _ (MonoidHom.id R) h hc s
#align preimage_smul_set preimage_smul_set

end Monoid

section Group

variable [Group R] [Group S]
variable (σ : R → S)
variable [MulAction R M] [MulAction S N] [MulAction R M₁] [MulAction R M₂]
variable {F : Type*} (h : F)

/-- Variant of `preimage_smul_setₛₗ` when R and S are groups
(does not require that `σ` belongs to some `MonoidHomClass`) -/
theorem preimage_smul_setₛₗ'
    [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply le_antisymm
  · intro m
    rintro ⟨n, hn, hn'⟩
    suffices n = σ c⁻¹ • h m by
      rw [mem_smul_set_iff_inv_smul_mem, mem_preimage, map_smulₛₗ, ← this]
      exact hn
    rw [smul_eq_iff_eq_inv_smul] at hn'
    rw [← map_smulₛₗ, hn', inv_smul_eq_iff, ← map_smulₛₗ, smul_inv_smul]
  · -- exact preimage_smul_setₛₗ_le (G := R → S) R M N σ h s
    intro m
    rw [mem_smul_set_iff_inv_smul_mem, mem_preimage]
    set m' := c⁻¹ • m with hm'
    rw [eq_inv_smul_iff] at hm'
    intro hm's
    rw [mem_preimage, ← hm', map_smulₛₗ]
    use h m'

variable (R)

-- There's a bug here, it should be possible to insert `@id R`
theorem preimage_smul_set' [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  -- ACL: was preimage_smul_setₛₗ _ _ _ h hc s
  preimage_smul_setₛₗ' _ _ (MonoidHom.id R) h c s
