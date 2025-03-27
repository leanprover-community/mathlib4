/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Positive linear maps

This file defines positive linear maps as a linear map that is also an order homomorphism.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

/-- A positive linear map is a linear map that is also an order homomorphism. -/
structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R] [OrderedAddCommMonoid E₁]
    [OrderedAddCommMonoid E₂] [Module R E₁] [Module R E₂] extends E₁ →ₗ[R] E₂, E₁ →o E₂

/-- The `OrderHom` underlying a `PositiveLinearMap`. -/
add_decl_doc PositiveLinearMap.toOrderHom

/-- Notation for a `PositiveLinearMap`. -/
notation:25 E " →P[" R:25 "] " F:0 => PositiveLinearMap R E F

/-- A positive linear map is a linear map that is also an order homomorphism. -/
class PositiveLinearMapClass (F : Type*) (R : outParam Type*) (E₁ E₂ : Type*) [Semiring R]
    [OrderedAddCommMonoid E₁] [OrderedAddCommMonoid E₂] [Module R E₁] [Module R E₂]
    [FunLike F E₁ E₂] extends LinearMapClass F R E₁ E₂, OrderHomClass F E₁ E₂

namespace PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R] [OrderedAddCommMonoid E₁] [OrderedAddCommMonoid E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [PositiveLinearMapClass F R E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
def toPositiveLinearMap (f : F) : E₁ →P[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂) with }

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
instance instCoeToLinearMap : CoeHead F (E₁ →P[R] E₂) where
  coe f := toPositiveLinearMap f

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ : Type*} [Semiring R] [OrderedAddCommMonoid E₁] [OrderedAddCommMonoid E₂]
  [Module R E₁] [Module R E₂]

instance : FunLike (E₁ →P[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : PositiveLinearMapClass (E₁ →P[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'
  map_rel f := fun {_ _} hab => f.monotone' hab



@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →P[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →P[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  _root_.map_nonneg f hx

end general

section addgroup

variable {R E₁ E₂ : Type*} [Semiring R] [OrderedAddCommGroup E₁] [OrderedAddCommGroup E₂]
  [Module R E₁] [Module R E₂]

/-- Define a positive map from a linear map that maps nonnegative elements to nonnegative
elements -/
def mk₀  (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →P[R] E₂ :=
  { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 ≤ f (b - a) := hf _ hab
      simpa using this }

end addgroup

end PositiveLinearMap
