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
    0 ≤ M.mapₗ toLinearMap

class KPositiveMapClass (F : Type*) (k : outParam ℕ) (A₁ : Type*) (A₂ : Type*)
    [FunLike F A₁ A₂] [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    extends LinearMapClass F ℂ A₁ A₂ where
  map_cstarMatrix_nonneg' (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.mapₗ (φ : A₁ →ₗ[ℂ] A₂)

namespace KPositiveMapClass

variable {F A₁ A₂ : Type*} {k : ℕ}  [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [KPositiveMapClass F k A₁ A₂]

--open CStarMatrix in
--lemma map_cstarMatrix_nonneg {n : Type*} [Fintype n] [DecidableEq n] (hn : Fintype.card n ≤ k) (φ : F)
--    (M : CStarMatrix n n A₁) (hM : 0 ≤ M) : 0 ≤ M.mapₗ (φ : A₁ →ₗ[ℂ] A₂) := by
--  let m := k - Fintype.card n
--  let e : n ⊕ (Fin m) ≃ Fin k := Fintype.equivFinOfCardEq <| by
--    simp only [Fintype.card_sum, Fintype.card_fin]
--    omega
--  set M' := M.mapₗ (φ : A₁ →ₗ[ℂ] A₂) with hM'
--  have h₃ : 0 ≤ reindexₐ ℂ e
--      ((fromBlocks M 0 0 (0 : CStarMatrix (Fin m) (Fin m) A₁)).mapₗ (φ : A₁ →ₗ[ℂ] A₂)) := by
--    rw [mapₗ_reindexₐ]
--    apply map_cstarMatrix_nonneg'
--    apply map_nonneg
--    exact fromBlocks_diagonal_nonneg hM le_rfl
--  rw [← OrderIsoClass.map_le_map_iff (reindexₐ ℂ A₁ e).symm] at h₃
--  --rw [fromBlocks_map] at h₃
--  --rw [map_le_map_iff] at h₃  -- COME ON!!
--  have hmain : 0 ≤ M.mapₗ (φ : A₁ →ₗ[ℂ] A₂) ∧ (0 : CStarMatrix (Fin m) (Fin m) A₂) ≤ 0 := by
--    rw [← fromBlocks_diagonal_le_iff]
--    simp only [fromBlocks_zero, mapₗ_apply, LinearMap.coe_coe]
--    sorry
--  exact hmain.1
--  --have h₁ : (0 : CStarMatrix (Fin m) (Fin m) A₁) ≤ 0 := le_rfl
--  --have h₂ : 0 ≤ (fromBlocks M 0 0 (0 : CStarMatrix (Fin m) (Fin m) A₁)).mapₗ (φ : A₁ →ₗ[ℂ] A₂) := by
--  --sorry
--  --have h₁ : 0 ≤ fromBlocks M 0 0 (0 : CStarMatrix (Fin m) (Fin m) A₁) := by sorry
--  --sorry

/-- Reinterpret an element of a type of k-positive linear maps as a k-positive linear map. -/
def toKPositiveLinearMap (f : F) : KPositiveMap k A₁ A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' M hM := KPositiveMapClass.map_cstarMatrix_nonneg' f M hM }

/-- Reinterpret an element of a type of k-positive linear maps as a k-positive linear map. -/
instance instCoeToKPositiveMap : CoeHead F (KPositiveMap k A₁ A₂) where
  coe f := toKPositiveLinearMap f

/-- A k-positive map is also k'-positive for any `k' < k`. -/
lemma toLowerK (k' : ℕ) (hk : k' < k) : KPositiveMapClass F k' A₁ A₂ where
  map_cstarMatrix_nonneg' φ M hM := by
    sorry

end KPositiveMapClass

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

/-- A completely positive map is k-positive for every k. This cannot be instance for arbitrary
`k`, and we only provide instances for 1 and 2 below. -/
lemma toKPositiveMapClass (k : ℕ) : KPositiveMapClass F k A₁ A₂ where
  map_cstarMatrix_nonneg' f M hM := map_cstarMatrix_nonneg' k f M hM

instance toTwoPositiveMapClass : KPositiveMapClass F 2 A₁ A₂ := toKPositiveMapClass 2
instance toOnePositiveMapClass : KPositiveMapClass F 1 A₁ A₂ := toKPositiveMapClass 1

end CompletelyPositiveMapClass
