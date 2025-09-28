/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise star operation on sets

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : Set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/


namespace Set

open Pointwise

local postfix:max "⋆" => star

variable {α : Type*} {s t : Set α} {a : α}

/-- The set `(star s : Set α)` is defined as `{x | star x ∈ s}` in the scope Pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`Set.image_star`. -/
protected def star [Star α] : Star (Set α) := ⟨preimage Star.star⟩

scoped[Pointwise] attribute [instance] Set.star

@[simp]
theorem star_empty [Star α] : (∅ : Set α)⋆ = ∅ := rfl

@[simp]
theorem star_univ [Star α] : (univ : Set α)⋆ = univ := rfl

@[simp]
theorem nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty :=
  star_involutive.surjective.nonempty_preimage

theorem Nonempty.star [InvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty :=
  nonempty_star.2 h

@[simp]
theorem mem_star [Star α] : a ∈ s⋆ ↔ a⋆ ∈ s := Iff.rfl

theorem star_mem_star [InvolutiveStar α] : a⋆ ∈ s⋆ ↔ a ∈ s := by simp only [mem_star, star_star]

@[simp]
theorem star_preimage [Star α] : Star.star ⁻¹' s = s⋆ := rfl

@[simp]
theorem image_star [InvolutiveStar α] : Star.star '' s = s⋆ := by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

@[simp]
theorem inter_star [Star α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ := preimage_inter

@[simp]
theorem union_star [Star α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ := preimage_union

@[simp]
theorem iInter_star {ι : Sort*} [Star α] (s : ι → Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
  preimage_iInter

@[simp]
theorem iUnion_star {ι : Sort*} [Star α] (s : ι → Set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
  preimage_iUnion

@[simp]
theorem compl_star [Star α] : sᶜ⋆ = s⋆ᶜ := preimage_compl

@[simp]
instance [InvolutiveStar α] : InvolutiveStar (Set α) where
  star := Star.star
  star_involutive s := by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

@[simp]
theorem star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t :=
  Equiv.star.surjective.preimage_subset_preimage_iff

theorem star_subset [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ := by
  rw [← star_subset_star, star_star]

theorem Finite.star [InvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite :=
  hs.preimage star_injective.injOn

theorem star_singleton {β : Type*} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} := by
  ext1 y
  rw [mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm]

protected theorem star_mul [Mul α] [StarMul α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]

protected theorem star_add [AddMonoid α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

@[simp]
instance [Star α] [TrivialStar α] : TrivialStar (Set α) where
  star_trivial s := by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

protected theorem star_inv [Group α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv]

protected theorem star_inv' [GroupWithZero α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [mem_star, mem_inv, star_inv₀]

end Set

@[simp]
lemma StarMemClass.star_coe_eq {S α : Type*} [InvolutiveStar α] [SetLike S α]
    [StarMemClass S α] (s : S) : star (s : Set α) = s := by
  ext x
  simp only [Set.mem_star, SetLike.mem_coe]
  exact ⟨by simpa only [star_star] using star_mem (s := s) (r := star x), star_mem⟩
