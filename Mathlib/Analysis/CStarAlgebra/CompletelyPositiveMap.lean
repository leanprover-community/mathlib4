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
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
    extends OrderHomClass F A₁ A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

/-- Notation for a `CompletelyPositiveMap`. -/
notation:25 A₁ " →CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
def toCompletelyPositiveLinearMap [CompletelyPositiveMapClass F A₁ A₂] (f : F) : A₁ →CP A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' k M hM := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' k f M hM }

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
instance instCoeToCompletelyPositiveMap [CompletelyPositiveMapClass F A₁ A₂] :
    CoeHead F (A₁ →CP A₂) where
  coe f := toCompletelyPositiveLinearMap f

open CStarMatrix in
/-- A completely positive map is also an order homomorphism. -/
lemma _root_.OrderHomClass.of_map_cstarMatrix_nonneg
    (h : ∀ (k : ℕ) (f : F) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map f) :
    OrderHomClass F A₁ A₂ := .ofLinear <| by
  intro f a ha
  let Ma := toOneByOne ℂ A₁ a
  have h₁ : 0 ≤ Ma := map_nonneg (toOneByOne ℂ A₁) ha
  have h₂ : 0 ≤ Ma.map f := h 1 f Ma h₁
  have h₃ : f a = (toOneByOne ℂ A₂).symm (toOneByOne ℂ A₂ (f a)) := rfl
  rw [h₃]
  exact map_nonneg (toOneByOne ℂ A₂).symm h₂

open CStarMatrix in
lemma of_map_cstarMatrix_nonneg
    (h : ∀ (k : ℕ) (f : F) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map f) :
    CompletelyPositiveMapClass F A₁ A₂ :=
  { OrderHomClass.of_map_cstarMatrix_nonneg h with
    map_cstarMatrix_nonneg' := h }

open CStarMatrix in
lemma map_cstarMatrix_nonneg [CompletelyPositiveMapClass F A₁ A₂] {n : Type*} [Fintype n]
    (φ : F) (M : CStarMatrix n n A₁) (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 ≤ (reindexₐ ℂ A₁ e M).mapₗ (φ : A₁ →ₗ[ℂ] A₂) := by
    refine CompletelyPositiveMapClass.map_cstarMatrix_nonneg' k _ _ (map_nonneg _ hM)
  rw [← mapₗ_reindexₐ] at hmain
  have hrw :
      reindexₐ ℂ A₂ e.symm ((reindexₐ ℂ A₂ e) (M.map (φ : A₁ → A₂))) = M.map (φ : A₁ → A₂) := by
    simp
  rw [← hrw]
  exact map_nonneg _ hmain

end CompletelyPositiveMapClass

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]
  [FunLike F A₁ A₂]
  [NonUnitalAlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix CFC in
instance instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' k f M hM := by
    change 0 ≤ (mapₙₐ (f : A₁ →⋆ₙₐ[ℂ] A₂)) M
    exact map_nonneg _ hM

end NonUnitalStarAlgHomClass
