/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # `k`-positive and completely positive maps

A positive linear map `φ` is called `k`-positive if `CStarMatrix.mapₗ (Fin k) (Fin k) φ`
(i.e. applying `φ` to all entries of a k × k matrix) is also positive. If this condition holds
for all `k`, then `φ` is called *completely positive*.

This file defines `k`-positive and completely positive maps.

## Main results

FIXME
-/

structure KPositiveMap (k : ℕ) (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ CStarMatrix.mapₗ toLinearMap M

class KPositiveMapClass (F : Type*) (k : outParam ℕ) (A₁ : Type*) (A₂ : Type*)
    [FunLike F A₁ A₂] [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    extends LinearMapClass F ℂ A₁ A₂ where
  map_cstarMatrix_nonneg' (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ CStarMatrix.mapₗ (φ : A₁ →ₗ[ℂ] A₂) M

namespace KPositiveMapClass

variable {F A₁ A₂ : Type*} {k : ℕ}  [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [KPositiveMapClass F k A₁ A₂]

/-- Reinterpret an element of a type of k-positive linear maps as a positive linear map. -/
def toKPositiveLinearMap (f : F) : KPositiveMap k A₁ A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' M hM := KPositiveMapClass.map_cstarMatrix_nonneg' f M hM }

/-- Reinterpret an element of a type of k-positive linear maps as a positive linear map. -/
instance instCoeToKPositiveMap : CoeHead F (KPositiveMap k A₁ A₂) where
  coe f := toKPositiveLinearMap f

end KPositiveMapClass

structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
      0 ≤ CStarMatrix.mapₗ toLinearMap M

class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [FunLike F A₁ A₂] [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    extends LinearMapClass F ℂ A₁ A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ CStarMatrix.mapₗ (φ : A₁ →ₗ[ℂ] A₂) M


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

end CompletelyPositiveMapClass
