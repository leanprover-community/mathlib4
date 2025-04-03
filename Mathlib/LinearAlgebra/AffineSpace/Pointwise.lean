/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

#align_import linear_algebra.affine_space.pointwise from "leanprover-community/mathlib"@"e96bdfbd1e8c98a09ff75f7ac6204d142debc840"

/-! # Pointwise instances on `AffineSubspace`s

This file provides the additive action `AffineSubspace.pointwiseAddAction` in the
`Pointwise` locale.

-/


open Affine Pointwise

open Set

namespace AffineSubspace

variable {k : Type*} [Ring k]
variable {V P V₁ P₁ V₂ P₂ : Type*}
variable [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P) where
  vadd x S := S.map (AffineEquiv.constVAdd k P x)
  zero_vadd p := ((congr_arg fun f => p.map f) <| AffineMap.ext <| zero_vadd _).trans p.map_id
  add_vadd _ _ p :=
    ((congr_arg fun f => p.map f) <| AffineMap.ext <| add_vadd _ _).trans (p.map_map _ _).symm
#align affine_subspace.pointwise_add_action AffineSubspace.pointwiseAddAction

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

open Pointwise

theorem pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) :
    v +ᵥ s = s.map (AffineEquiv.constVAdd k P v) :=
  rfl

@[simp]
theorem coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ (s : Set P) :=
  rfl
#align affine_subspace.coe_pointwise_vadd AffineSubspace.coe_pointwise_vadd

theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff
#align affine_subspace.vadd_mem_pointwise_vadd_iff AffineSubspace.vadd_mem_pointwise_vadd_iff

theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by
  ext; simp [pointwise_vadd_eq_map, map_bot]
#align affine_subspace.pointwise_vadd_bot AffineSubspace.pointwise_vadd_bot

theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  rw [pointwise_vadd_eq_map, map_direction]
  exact Submodule.map_id _
#align affine_subspace.pointwise_vadd_direction AffineSubspace.pointwise_vadd_direction

theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s
#align affine_subspace.pointwise_vadd_span AffineSubspace.pointwise_vadd_span

theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  erw [pointwise_vadd_eq_map, pointwise_vadd_eq_map, map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _
#align affine_subspace.map_pointwise_vadd AffineSubspace.map_pointwise_vadd

end AffineSubspace
