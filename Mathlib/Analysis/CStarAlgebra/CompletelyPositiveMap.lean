/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-! # Completely positive maps

A linear map `φ : A₁ →ₗ[ℂ] A₂` (where `A₁` and `A₂` are C⋆-algebras) is called
*completely positive (CP)* if `CStarMatrix.map (Fin k) (Fin k) φ` (i.e. applying `φ` to all
entries of a k × k matrix) is also positive for every `k : ℕ`.

This file defines completely positive maps and develops their basic API.

## Main results

+ `NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`: Non-unital star algebra
  homomorphisms are completely positive.

## Notation

+ `A₁ →CP A₂` denotes the type of CP maps from `A₁` to `A₂`. This notation is scoped to
  `CStarAlgebra`.

## Implementation notes

The morphism class `CompletelyPositiveMapClass` is designed to be part of the order hierarchy,
and only includes the order property; linearity is not mentioned at all. It is therefore meant
to be used in conjunction with `LinearMapClass`. This is meant to avoid mixing order and algebra
as much as possible.
-/

@[expose] public section

open scoped CStarAlgebra

/--
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and introduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a version of the
property that holds for matrices indexed by any finite type.
-/
structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
      0 ≤ M.map toLinearMap

/--
A linear map `φ : A₁ →ₗ[ℂ] A₂`  is called *completely positive (CP)* if
`CStarMatrix.mapₗ (Fin k) (Fin k) φ` (i.e. applying `φ` to all entries of a k × k matrix) is also
positive for every `k ∈ ℕ`.

Note that `Fin k` here is hardcoded to avoid having to quantify over types and introduce a new
universe parameter. See `CompletelyPositiveMap.map_cstarMatrix_nonneg` for a version of the
property that holds for matrices indexed by any finite type.
-/
class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] where
  map_cstarMatrix_nonneg' (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

/-- Notation for a `CompletelyPositiveMap`. -/
scoped[CStarAlgebra] notation:25 A₁ " →CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
@[coe]
def toCompletelyPositiveLinearMap [CompletelyPositiveMapClass F A₁ A₂] (f : F) : A₁ →CP A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' f }

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
map. -/
instance instCoeToCompletelyPositiveMap [CompletelyPositiveMapClass F A₁ A₂] :
    CoeHead F (A₁ →CP A₂) where
  coe f := toCompletelyPositiveLinearMap f

set_option backward.isDefEq.respectTransparency false in
open CStarMatrix in
/-- Linear maps which are completely positive are order homomorphisms (i.e., positive maps). -/
lemma _root_.OrderHomClass.of_map_cstarMatrix_nonneg
    (h : ∀ (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map φ) :
    OrderHomClass F A₁ A₂ := .of_addMonoidHom <| by
  intro φ a ha
  simpa using map_nonneg (toOneByOne (Fin 1) ℂ A₂).symm <|
    h φ 1 _ <| map_nonneg (toOneByOne (Fin 1) ℂ A₁) ha

instance [CompletelyPositiveMapClass F A₁ A₂] : OrderHomClass F A₁ A₂ :=
  .of_map_cstarMatrix_nonneg CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]

instance : FunLike (A₁ →CP A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : LinearMapClass (A₁ →CP A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

instance : CompletelyPositiveMapClass (A₁ →CP A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

open CStarMatrix in
lemma map_cstarMatrix_nonneg {n : Type*} [Fintype n] (φ : A₁ →CP A₂) (M : CStarMatrix n n A₁)
    (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 ≤ (reindexₐ ℂ A₁ e M).mapₗ (φ : A₁ →ₗ[ℂ] A₂) := by
    simp only [mapₗ, LinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
    exact CompletelyPositiveMapClass.map_cstarMatrix_nonneg' _ k _ (map_nonneg _ hM)
  rw [← mapₗ_reindexₐ] at hmain
  simpa [reindexₐ_symm] using map_nonneg (reindexₐ ℂ A₂ e).symm hmain

end CompletelyPositiveMap

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [NonUnitalAlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix CFC in
/-- Non-unital star algebra homomorphisms are completely positive. -/
instance instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' φ k M hM := by
    change 0 ≤ (mapₙₐ (φ : A₁ →⋆ₙₐ[ℂ] A₂)) M
    exact map_nonneg _ hM

end NonUnitalStarAlgHomClass
