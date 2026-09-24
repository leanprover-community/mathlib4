/-
Copyright (c) 2026 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Range of affine maps

The range of an affine map `f : P₁ →ᵃ[R] P₂` is an affine subspace of `P₂`.

# Implementation note

Follows `LinearMap.range`.

-/

@[expose] public section

open Affine Module AffineMap AffineSubspace

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

/-- The range of an affine map is nonempty. -/
instance instNonemptyRange : Nonempty (range f) :=
  Set.instNonemptyRange f

@[simp, norm_cast]
theorem coe_range : f.range = Set.range f := rfl

@[simp]
theorem mem_range (x : P₂) : x ∈ f.range ↔ ∃ (y : P₁), f y = x :=
  Iff.rfl

theorem range_eq_map_top : f.range = .map f ⊤ := by ext; simp

theorem mem_range_self (x : P₁) : f x ∈ f.range := by simp

@[simp]
theorem range_id : (id R P₁).range = ⊤ := by ext; simp

theorem range_direction_eq_linear_range : f.range.direction = f.linear.range := by
  rw [range_eq_map_top, map_direction, direction_top, Submodule.map_top]

/-- Restrict the codomain of an affine map `f` to `f.range`. -/
def rangeRestrict : P₁ →ᵃ[R] f.range where
  toFun p := ⟨f p, p, rfl⟩
  linear := f.linear.codRestrict f.range.direction
    (f.range_direction_eq_linear_range ▸ f.linear.mem_range_self)
  map_vadd' _ _ := by ext; simp [map_vadd]

theorem surjective_rangeRestrict : Function.Surjective ⇑f.rangeRestrict :=
  fun ⟨_, y, rfl⟩ => ⟨y, rfl⟩

@[simp]
theorem range_rangeRestrict : f.rangeRestrict.range = ⊤ := by
  ext ⟨_, x, rfl⟩
  simpa [AffineSubspace.mem_top, iff_true] using ⟨x, rfl⟩

@[simp]
theorem injective_rangeRestrict_iff :
    Function.Injective (rangeRestrict f) ↔ Function.Injective f := by
  convert (Function.Injective.of_comp_iff Subtype.val_injective f.rangeRestrict).symm
  ext; simp [rangeRestrict]

end AffineMap

end
