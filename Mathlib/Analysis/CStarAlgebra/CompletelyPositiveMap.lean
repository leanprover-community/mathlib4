/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Completely positive maps

A positive linear map `φ : A₁ →ₗ[ℂ] A₂` (where `A₁` and `A₂` are C⋆-algebras) is called
*completely positive (CP)* if `CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all
entries of a k × k matrix) is also positive for every `k ∈ ℕ`.

This file defines completely positive maps and develops their basic API.

## Main results

+ Non-unital star algebra homomorphisms are completely positive.

## Notation

+ `A₁ →CP A₂` denotes the type of CP maps from `A₁` to `A₂`.
-/

structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
      0 ≤ M.mapₗ toLinearMap

class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [FunLike F A₁ A₂] [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    extends LinearMapClass F ℂ A₁ A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.mapₗ (φ : A₁ →ₗ[ℂ] A₂)


/-- Notation for a `CompletelyPositiveMap`. -/
notation:25 A₁ " →CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [CompletelyPositiveMapClass F A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
def toCompletelyPositiveLinearMap (f : F) : A₁ →CP A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' k M hM := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' k f M hM }

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
instance instCoeToCompletelyPositiveMap : CoeHead F (A₁ →CP A₂) where
  coe f := toCompletelyPositiveLinearMap f

open CStarMatrix in
/-- A completely positive map is also positive. -/
instance instPositiveLinearMapClass : PositiveLinearMapClass F ℂ A₁ A₂ := .mk₀ <| by
  intro f a ha
  let Ma := toOneByOne ℂ A₁ a
  have h₁ : 0 ≤ Ma := map_nonneg (toOneByOne ℂ A₁) ha
  have h₂ : 0 ≤ Ma.map f := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' 1 f Ma h₁
  have h₃ : f a = (toOneByOne ℂ A₂).symm (toOneByOne ℂ A₂ (f a)) := rfl
  rw [h₃]
  exact map_nonneg (toOneByOne ℂ A₂).symm h₂

end CompletelyPositiveMapClass

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂]
  [LinearMapClass F ℂ A₁ A₂]  -- This is implied by `NonUnitalAlgHomClass` but it fails without it
  [NonUnitalAlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix CFC in
instance instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' k f M hM := by
    let fM : CStarMatrix (Fin k) (Fin k) A₂ := ofMatrix fun i j => f (sqrt M i j)
    have hfM : fM * fM = ofMatrix fun i j ↦ ∑ x, f (sqrt M i x) * f (sqrt M x j) := by
      ext
      simp [mul_apply, fM]
    have hfM' : fM = star fM := by
      ext
      simp [fM, star_eq_conjTranspose, ← map_star]
      rw [star_apply_of_isSelfAdjoint (by cfc_tac)]
    rw [← sqrt_mul_sqrt_self M, mapₗ]
    dsimp
    simp only [map, mul_apply, map_sum, map_mul, ← hfM]
    nth_rewrite 1 [hfM']
    exact star_mul_self_nonneg fM

end NonUnitalStarAlgHomClass
