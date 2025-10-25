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

## Implementation notes

We do not define `PositiveLinearMapClass` to avoid adding a class that mixes order and algebra.
One can achieve the same effect by using a combination of `LinearMapClass` and `OrderHomClass`.
We nevertheless use the namespace for lemmas using that combination of typeclasses.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

/-- A positive linear map is a linear map that is also an order homomorphism. -/
structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₗ[R] E₂, E₁ →o E₂

/-- The `OrderHom` underlying a `PositiveLinearMap`. -/
add_decl_doc PositiveLinearMap.toOrderHom

/-- Notation for a `PositiveLinearMap`. -/
notation:25 E " →ₚ[" R:25 "] " F:0 => PositiveLinearMap R E F

namespace PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
def toPositiveLinearMap (f : F) : E₁ →ₚ[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂) with }

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
instance instCoeToLinearMap : CoeHead F (E₁ →ₚ[R] E₂) where
  coe f := toPositiveLinearMap f

/-- An additive group homomorphism that maps nonnegative elements to nonnegative elements
is an order homomorphism. -/
lemma _root_.OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : ∀ f : F', ∀ x, 0 ≤ x → 0 ≤ f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

@[deprecated (since := "2025-09-13")] alias _root_.OrderHomClass.ofLinear :=
  OrderHomClass.of_addMonoidHom

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

instance : FunLike (E₁ →ₚ[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

@[ext]
lemma ext {f g : E₁ →ₚ[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance : LinearMapClass (E₁ →ₚ[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

instance : OrderHomClass (E₁ →ₚ[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →ₚ[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →ₚ[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  _root_.map_nonneg f hx

end general

section addgroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂]

/-- Define a positive map from a linear map that maps nonnegative elements to nonnegative
elements -/
def mk₀ (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →ₚ[R] E₂ :=
  { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 ≤ f (b - a) := hf _ hab
      simpa using this }

end addgroup

end PositiveLinearMap
