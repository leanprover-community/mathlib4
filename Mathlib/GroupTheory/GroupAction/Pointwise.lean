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

- `preimage_smul_setₛₗ'`, `preimage_smul_setₛₗ`, `preimage_smul_set`
`preimage_smul_set` :
one has `h ⁻¹' (σ c • s) = c • h⁻¹' s`

-/

open Set Pointwise

theorem MulAction.smul_bijective_of_is_unit
    {M : Type*} [Monoid M] {α : Type*} [MulAction M α] {m : M} (hm : IsUnit m) :
    Function.Bijective (fun (a : α) ↦ m • a) := by
  lift m to Mˣ using hm
  rw [Function.bijective_iff_has_inverse]
  use (fun (a : α) ↦ m⁻¹ • a)
  constructor
  intro x; simp [← Units.smul_def]
  intro x; simp [← Units.smul_def]

variable {R S : Type*} (M M₁ M₂ N : Type*)

variable [Monoid R] [Monoid S] (σ : R → S)
variable [MulAction R M] [MulAction S N] [MulAction R M₁] [MulAction R M₂]
variable {F : Type*} (h : F)

-- @[simp] -- In #8386, the `simp_nf` linter complains:
-- "Left-hand side does not simplify, when using the simp lemma on itself."
-- For now we will have to manually add `image_smul_setₛₗ _` to the `simp` argument list.
-- TODO: when lean4#3107 is fixed, mark this as `@[simp]`.
theorem image_smul_setₛₗ [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set M) :
    h '' (c • s) = σ c • h '' s := by
  simp only [← image_smul, image_image, map_smulₛₗ h]
#align image_smul_setₛₗ image_smul_setₛₗ

/-- Translation of preimage is contained in preimage of translation -/
theorem smul_preimage_set_leₛₗ
    [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (t : Set N) :
    c • h ⁻¹' t ⊆ h ⁻¹' (σ c • t) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨h y, hy, (by rw [map_smulₛₗ])⟩

/-- General version of `preimage_smul_setₛₗ` -/
theorem preimage_smul_setₛₗ'
    [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set N)
    (hc : Function.Surjective (fun (m : M) ↦ c • m))
    (hc' : Function.Injective (fun (n : N) ↦ σ c • n)) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply le_antisymm
  · intro m
    obtain ⟨m', rfl⟩ := hc m
    rintro ⟨n, hn, hn'⟩
    refine ⟨m', ?_, rfl⟩
    rw [map_smulₛₗ] at hn'
    rw [mem_preimage, ← hc' hn']
    exact hn
  · exact smul_preimage_set_leₛₗ  M N σ h c s

/-- `preimage_smul_setₛₗ` when both scalars act by unit -/
theorem preimage_smul_setₛₗ_of_units
    [FunLike F M N] [MulActionSemiHomClass F σ M N]
    {c : R} (hc : IsUnit c) (hc' : IsUnit (σ c)) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply preimage_smul_setₛₗ'
  · exact (MulAction.smul_bijective_of_is_unit hc).surjective
  · exact (MulAction.smul_bijective_of_is_unit hc').injective
#align preimage_smul_setₛₗ preimage_smul_setₛₗ

/-- `preimage_smul_setₛₗ` in the context of a `MonoidHom` -/
theorem MonoidHom.preimage_smul_setₛₗ (σ : R →* S)
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F ⇑σ M N]
  {c : R} (hc : IsUnit c) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply preimage_smul_setₛₗ_of_units σ h c s hc
  · sorry

/-- `preimage_smul_setₛₗ` in the context of a `MonoidHomClass` -/
theorem MonoidHomClass.preimage_smul_setₛₗ_of_units
  {G : Type*} [FunLike G R S] [MonoidHomClass G R S] (σ : G)
  [MulAction R M] [MulAction S N]
  {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N]
  {c : R} (hc : IsUnit c) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s :=
 MonoidHom.preimage_smul_setₛₗ (σ : R →* S) h c s hc

/-- `preimage_smul_setₛₗ` in the context of a groups -/
theorem Group.preimage_smul_setₛₗ
    {R S : Type*} [Group R] [Group S] (σ : R → S)
    [MulAction R M] [MulAction S N]
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set N) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s :=
 preimage_smul_setₛₗ_of_units σ h c s hc (Group.isUnit _) (Group.isUnit _)

variable (R)

@[simp] -- This can be safely removed as a `@[simp]` lemma if `image_smul_setₛₗ` is readded.
theorem image_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₁) :
    h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s
#align image_smul_set image_smul_set

theorem smul_preimage_set_le
    [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (t : Set M₂) :
    c • h ⁻¹' t ⊆ h ⁻¹' (c • t) :=
  smul_preimage_set_leₛₗ _ _ _ h c t

theorem preimage_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  preimage_smul_setₛₗ _ _ _ h hc hc s
#align preimage_smul_set preimage_smul_set

theorem Group.preimage_smul_set [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  preimage_smul_set _ _ _ h (Group.isUnit ) s
#align preimage_smul_set preimage_smul_set
