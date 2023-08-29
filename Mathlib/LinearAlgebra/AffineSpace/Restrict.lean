/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

#align_import linear_algebra.affine_space.restrict from "leanprover-community/mathlib"@"09258fb7f75d741b7eda9fa18d5c869e2135d9f1"

/-!
# Affine map restrictions

This file defines restrictions of affine maps.

## Main definitions

* The domain and codomain of an affine map can be restricted using
  `AffineMap.restrict`.

## Main theorems

* The associated linear map of the restriction is the restriction of the
  linear map associated to the original affine map.
* The restriction is injective if the original map is injective.
* The restriction in surjective if the codomain is the image of the domain.
-/


variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

-- not an instance because it loops with `Nonempty`
theorem AffineSubspace.nonempty_map {E : AffineSubspace k P₁} [Ene : Nonempty E] {φ : P₁ →ᵃ[k] P₂} :
    Nonempty (E.map φ) := by
  obtain ⟨x, hx⟩ := id Ene
  -- ⊢ Nonempty { x // x ∈ map φ E }
  refine' ⟨⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩
  -- 🎉 no goals
#align affine_subspace.nonempty_map AffineSubspace.nonempty_map

-- Porting note: removed "local nolint fails_quickly" attribute
attribute [local instance] AffineSubspace.nonempty_map AffineSubspace.toAddTorsor

/-- Restrict domain and codomain of an affine map to the given subspaces. -/
def AffineMap.restrict (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
    [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) : E →ᵃ[k] F := by
  refine' ⟨_, _, _⟩
  · exact fun x => ⟨φ x, hEF <| AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
    -- 🎉 no goals
  · refine' φ.linear.restrict (_ : E.direction ≤ F.direction.comap φ.linear)
    -- ⊢ AffineSubspace.direction E ≤ Submodule.comap φ.linear (AffineSubspace.direct …
    rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
    -- ⊢ AffineSubspace.direction (AffineSubspace.map φ E) ≤ AffineSubspace.direction F
    exact AffineSubspace.direction_le hEF
    -- 🎉 no goals
  · intro p v
    -- ⊢ { val := ↑φ ↑(v +ᵥ p), property := (_ : ↑φ ↑(v +ᵥ p) ∈ ↑F) } = ↑(LinearMap.r …
    simp only [Subtype.ext_iff, Subtype.coe_mk, AffineSubspace.coe_vadd]
    -- ⊢ ↑φ (↑v +ᵥ ↑p) = ↑(↑(LinearMap.restrict φ.linear (_ : AffineSubspace.directio …
    apply AffineMap.map_vadd
    -- 🎉 no goals
#align affine_map.restrict AffineMap.restrict

theorem AffineMap.restrict.coe_apply (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) (x : E) :
    ↑(φ.restrict hEF x) = φ x :=
  rfl
#align affine_map.restrict.coe_apply AffineMap.restrict.coe_apply

theorem AffineMap.restrict.linear_aux {φ : P₁ →ᵃ[k] P₂} {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} (hEF : E.map φ ≤ F) : E.direction ≤ F.direction.comap φ.linear := by
  rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
  -- ⊢ AffineSubspace.direction (AffineSubspace.map φ E) ≤ AffineSubspace.direction F
  exact AffineSubspace.direction_le hEF
  -- 🎉 no goals
#align affine_map.restrict.linear_aux AffineMap.restrict.linear_aux

theorem AffineMap.restrict.linear (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) :
    (φ.restrict hEF).linear = φ.linear.restrict (AffineMap.restrict.linear_aux hEF) :=
  rfl
#align affine_map.restrict.linear AffineMap.restrict.linear

theorem AffineMap.restrict.injective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Injective φ)
    {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F]
    (hEF : E.map φ ≤ F) : Function.Injective (AffineMap.restrict φ hEF) := by
  intro x y h
  -- ⊢ x = y
  simp only [Subtype.ext_iff, Subtype.coe_mk, AffineMap.restrict.coe_apply] at h ⊢
  -- ⊢ ↑x = ↑y
  exact hφ h
  -- 🎉 no goals
#align affine_map.restrict.injective AffineMap.restrict.injective

theorem AffineMap.restrict.surjective (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (h : E.map φ = F) :
    Function.Surjective (AffineMap.restrict φ (le_of_eq h)) := by
  rintro ⟨x, hx : x ∈ F⟩
  -- ⊢ ∃ a, ↑(restrict φ (_ : AffineSubspace.map φ E ≤ F)) a = { val := x, property …
  rw [← h, AffineSubspace.mem_map] at hx
  -- ⊢ ∃ a, ↑(restrict φ (_ : AffineSubspace.map φ E ≤ F)) a = { val := x, property …
  obtain ⟨y, hy, rfl⟩ := hx
  -- ⊢ ∃ a, ↑(restrict φ (_ : AffineSubspace.map φ E ≤ F)) a = { val := ↑φ y, prope …
  exact ⟨⟨y, hy⟩, rfl⟩
  -- 🎉 no goals
#align affine_map.restrict.surjective AffineMap.restrict.surjective

theorem AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ →ᵃ[k] P₂}
    (hφ : Function.Injective φ) : Function.Bijective (φ.restrict (le_refl (E.map φ))) :=
  ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩
#align affine_map.restrict.bijective AffineMap.restrict.bijective
