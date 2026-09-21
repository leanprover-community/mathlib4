/-
Copyright (c) 2026 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Range of linear maps

The range of an affine map `f : P₁ →ᵃ[R] P₂` is an affine subspace of `P₂`.
-/

@[expose] public section

open Affine Module AffineMap

section

variable {R V₁ V₂ P₁ P₂ : Type*}

namespace AffineMap

variable [Ring R]
variable [AddCommGroup V₁] [Module R V₁]
variable [AddCommGroup V₂] [Module R V₂]
variable [AffineSpace V₁ P₁] [AffineSpace V₂ P₂]

variable (f : P₁ →ᵃ[R] P₂)

/-- The range of an affine map is an affine subspace. -/
def range : AffineSubspace R P₂ where
  carrier := Set.range f
  smul_vsub_vadd_mem' := by
    simp only [Set.mem_range, forall_exists_index]
    intro c _ _ _ x₁ h₁ x₂ h₂ x₃ h₃
    exact ⟨c • (x₁ -ᵥ x₂) +ᵥ x₃, by simp [map_vadd, ← h₁, ← h₂, ← h₃]⟩

instance instNonemptyRange : Nonempty (range f) :=
  Set.instNonemptyRange f

theorem coe_range : f.range = Set.range f := rfl

@[simp]
theorem mem_range (x : P₂) : x ∈ f.range ↔ ∃ (y : P₁), f y = x :=
  Iff.rfl

theorem range_eq_copmap_top : f.range = .map f ⊤ := by ext; simp

theorem mem_range_self (x : P₁) : f x ∈ f.range := by simp

@[simp]
theorem range_id : (id R P₁).range = ⊤ := by ext; simp

theorem range_direction_eq_linear_range : f.range.direction = f.linear.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro _ ⟨p₁, h₁, p₂, h₂, h⟩
    simp only [SetLike.mem_coe, mem_range] at h₁ h₂
    obtain ⟨p₁, rfl⟩ := h₁
    obtain ⟨p₂, rfl⟩ := h₂
    exact ⟨p₁ -ᵥ p₂, h ▸ f.linearMap_vsub _ _⟩
  · apply Submodule.span_le.mp
    intro v hv
    rw [Submodule.span_coe_eq_restrictScalars] at hv
    obtain ⟨w, rfl⟩ := hv
    apply Submodule.subset_span
    simp only [Set.mem_vsub, SetLike.mem_coe, mem_range, exists_exists_eq_and]
    exact ⟨(w +ᵥ Classical.arbitrary P₁), (Classical.arbitrary P₁), by simp⟩

/-- Restrict the codomain of an affine map `f` to `f.range`. -/
def rangeRestrict : P₁ →ᵃ[R] f.range where
  toFun p := ⟨f p, p, rfl⟩
  linear := (LinearEquiv.ofEq _ _ f.range_direction_eq_linear_range.symm).toLinearMap ∘ₗ
    f.linear.rangeRestrict
  map_vadd' _ _ := by ext; simp [map_vadd]

@[simp]
theorem range_rangeRestrict : f.rangeRestrict.range = ⊤ := by
  ext ⟨_, x, rfl⟩
  simpa [AffineSubspace.mem_top, iff_true] using ⟨x, rfl⟩

theorem ker_rangeRestrict : f.rangeRestrict ⁻¹' ⊥ = f ⁻¹' ⊥ := by simp

theorem surjective_rangeRestrict : Function.Surjective ⇑f.rangeRestrict := by
  intro ⟨x, ⟨y, hy⟩⟩
  use y; simp [rangeRestrict, hy]

@[simp]
lemma injective_rangeRestrict_iff :
    (rangeRestrict f).toFun.Injective ↔ f.toFun.Injective := by
  constructor <;> intro h _ _ hpq <;> apply h
  · exact Subtype.ext hpq
  · exact congrArg Subtype.val hpq

end AffineMap

end
