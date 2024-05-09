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

- `image_smul_setₛₗ` : under a `σ`-equivariant map,
  one has `h '' (c • s) = (σ c) • h '' s`.

- `preimage_smul_setₛₗ'` is a general version of the equality
  `h ⁻¹' (σ c • s) = c • h⁻¹' s`.
  It requires that `c` acts surjectively and `σ c` acts injectively and
  is provided with specific versions:
  - `preimage_smul_setₛₗ_of_units` when `c` and `σ c` are units
  - `preimage_smul_setₛₗ` when `σ` belongs to a `MonoidHomClass`and `c` is a unit
  - `MonoidHom.preimage_smul_setₛₗ` when `σ` is a `MonoidHom` and `c` is a unit
  - `Group.preimage_smul_setₛₗ` : when the types of `c` and `σ c` are groups.

- `image_smul_set`, `preimage_smul_set` and `Group.preimage_smul_set` are
  the variants when `σ` is the identity.

-/

open Set Pointwise

theorem MulAction.smul_bijective_of_is_unit
    {M : Type*} [Monoid M] {α : Type*} [MulAction M α] {m : M} (hm : IsUnit m) :
    Function.Bijective (fun (a : α) ↦ m • a) := by
  lift m to Mˣ using hm
  rw [Function.bijective_iff_has_inverse]
  use fun a ↦ m⁻¹ • a
  constructor
  · intro x; simp [← Units.smul_def]
  · intro x; simp [← Units.smul_def]

variable {R S : Type*} (M M₁ M₂ N : Type*)

variable [Monoid R] [Monoid S] (σ : R → S)
variable [MulAction R M] [MulAction S N] [MulAction R M₁] [MulAction R M₂]
variable {F : Type*} (h : F)

section MulActionSemiHomClass

variable [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set M) (t : Set N)

-- @[simp] -- In #8386, the `simp_nf` linter complains:
-- "Left-hand side does not simplify, when using the simp lemma on itself."
-- For now we will have to manually add `image_smul_setₛₗ _` to the `simp` argument list.
-- TODO: when lean4#3107 is fixed, mark this as `@[simp]`.
theorem image_smul_setₛₗ :
    h '' (c • s) = σ c • h '' s := by
  simp only [← image_smul, image_image, map_smulₛₗ h]
#align image_smul_setₛₗ image_smul_setₛₗ

/-- Translation of preimage is contained in preimage of translation -/
theorem smul_preimage_set_leₛₗ :
    c • h ⁻¹' t ⊆ h ⁻¹' (σ c • t) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨h y, hy, by rw [map_smulₛₗ]⟩

variable {c}

/-- General version of `preimage_smul_setₛₗ` -/
theorem preimage_smul_setₛₗ'
    (hc : Function.Surjective (fun (m : M) ↦ c • m))
    (hc' : Function.Injective (fun (n : N) ↦ σ c • n)) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t := by
  apply le_antisymm
  · intro m
    obtain ⟨m', rfl⟩ := hc m
    rintro ⟨n, hn, hn'⟩
    refine ⟨m', ?_, rfl⟩
    rw [map_smulₛₗ] at hn'
    rw [mem_preimage, ← hc' hn']
    exact hn
  · exact smul_preimage_set_leₛₗ M N σ h c t

/-- `preimage_smul_setₛₗ` when both scalars act by unit -/
theorem preimage_smul_setₛₗ_of_units (hc : IsUnit c) (hc' : IsUnit (σ c)) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t := by
  apply preimage_smul_setₛₗ'
  · exact (MulAction.smul_bijective_of_is_unit hc).surjective
  · exact (MulAction.smul_bijective_of_is_unit hc').injective
#align preimage_smul_setₛₗ preimage_smul_setₛₗ_of_units


/-- `preimage_smul_setₛₗ` in the context of a `MonoidHom` -/
theorem MonoidHom.preimage_smul_setₛₗ (σ : R →* S)
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F ⇑σ M N] (h : F)
    {c : R} (hc : IsUnit c) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units M N σ h t hc (IsUnit.map σ hc)

/-- `preimage_smul_setₛₗ` in the context of a `MonoidHomClass` -/
theorem preimage_smul_setₛₗ
    {G : Type*} [FunLike G R S] [MonoidHomClass G R S] (σ : G)
    [MulAction R M] [MulAction S N]
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N] (h : F)
    {c : R} (hc : IsUnit c) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
 MonoidHom.preimage_smul_setₛₗ M N (σ : R →* S) h hc t

/-- `preimage_smul_setₛₗ` in the context of a groups -/
theorem Group.preimage_smul_setₛₗ
    {R S : Type*} [Group R] [Group S] (σ : R → S)
    [MulAction R M] [MulAction S N]
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N] (h : F)
    (c : R) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units M N σ h t (Group.isUnit _) (Group.isUnit _)

end MulActionSemiHomClass

section MulActionHomClass

variable (R)
variable [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₁) (t : Set M₂)

@[simp] -- This can be safely removed as a `@[simp]` lemma if `image_smul_setₛₗ` is readded.
theorem image_smul_set :
    h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s
#align image_smul_set image_smul_set

theorem smul_preimage_set_le :
    c • h ⁻¹' t ⊆ h ⁻¹' (c • t) :=
  smul_preimage_set_leₛₗ _ _ _ h c t

variable {c}

theorem preimage_smul_set (hc : IsUnit c) :
    h ⁻¹' (c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units _ _ _ h t hc hc
#align preimage_smul_set preimage_smul_set

theorem Group.preimage_smul_set
    {R : Type*} [Group R] (M₁ M₂ : Type*)
    [MulAction R M₁] [MulAction R M₂]
    {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (h : F)
    (c : R) (t : Set M₂) :
    h ⁻¹' (c • t) = c • h ⁻¹' t :=
  _root_.preimage_smul_set R M₁ M₂ h t (Group.isUnit c)

end MulActionHomClass
