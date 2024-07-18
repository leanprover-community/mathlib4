/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

/-! # Pointwise instances on `AffineSubspace`s

This file provides the additive action `AffineSubspace.pointwiseAddAction` in the
`Pointwise` locale.

-/


open Affine Pointwise

open Set

variable {k V P V₁ P₁ V₂ P₂ : Type*}

namespace AffineSubspace
section Ring
variable [Ring k]
variable [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseVAdd : VAdd V (AffineSubspace k P) where
  vadd x s := s.map (AffineEquiv.constVAdd k P x)

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseVAdd

@[simp, norm_cast] lemma coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ (s : Set P) := rfl

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P) :=
  SetLike.coe_injective.addAction _ coe_pointwise_vadd

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

theorem pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) :
    v +ᵥ s = s.map (AffineEquiv.constVAdd k P v) :=
  rfl

theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff

@[simp] theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by
  ext; simp [pointwise_vadd_eq_map, map_bot]

@[simp] lemma pointwise_vadd_top (v : V) : v +ᵥ (⊤ : AffineSubspace k P) = ⊤ := by
  ext; simp [pointwise_vadd_eq_map, map_top, vadd_eq_iff_eq_neg_vadd]

theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  rw [pointwise_vadd_eq_map, map_direction]
  exact Submodule.map_id _

theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s

theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  erw [pointwise_vadd_eq_map, pointwise_vadd_eq_map, map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _

end Ring

section CommRing
variable [CommRing k] [AddCommGroup V] [Module k V] {a : k}

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseSMul : SMul k (AffineSubspace k V) where
  smul a s := s.map (LinearMap.lsmul _ _ a).toAffineMap

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseSMul

@[simp, norm_cast]
lemma coe_smul (a : k) (s : AffineSubspace k V) : ↑(a • s) = a • (s : Set V) := rfl

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale. -/
protected def mulAction : MulAction k (AffineSubspace k V) :=
  SetLike.coe_injective.mulAction _ coe_smul

scoped[Pointwise] attribute [instance] AffineSubspace.mulAction

lemma smul_eq_map (a : k) (s : AffineSubspace k V) :
    a • s = s.map (LinearMap.lsmul _ _ a).toAffineMap := rfl

lemma smul_mem_smul_iff (ha : IsUnit a) {s : AffineSubspace k V} {p : V} :
    a • p ∈ a • s ↔ p ∈ s := smul_mem_smul_set_iff (a := ha.unit)

@[simp] lemma smul_bot (a : k) : a • (⊥ : AffineSubspace k V) = ⊥ := by
  ext; simp [smul_eq_map, map_bot]

@[simp] lemma smul_top (ha : IsUnit a) : a • (⊤ : AffineSubspace k V) = ⊤ := by
  ext x; simpa [smul_eq_map, map_top] using ⟨ha.unit⁻¹ • x, smul_inv_smul ha.unit _⟩

lemma smul_span (a : k) (s : Set V) : a • affineSpan k s = affineSpan k (a • s) := map_span _ s

end CommRing

section Field
variable [Field k] [AddCommGroup V] [Module k V] {a : k}

lemma smul_direction (ha : a ≠ 0) (s : AffineSubspace k V) : (a • s).direction = s.direction := by
  rw [smul_eq_map, map_direction]
  change Submodule.map (a • LinearMap.id) _ = _
  simp [Submodule.map_smul, ha]

  end Field
end AffineSubspace
