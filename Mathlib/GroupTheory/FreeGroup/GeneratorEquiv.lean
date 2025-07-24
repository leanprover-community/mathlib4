/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Isomorphisms between free groups come from equivalences of their generators

This file proves that an isomorphism `e : G ≃* H` between free groups `G` and `H` is induced by an
equivalence of generators.

## TODO

We currently construct the equivalence of generators, but don't show that it induces the isomorphism
of groups.
-/

noncomputable section

variable {α β G H : Type*}

open IsFreeGroup Module

/-- `A` is a basis of the ℤ-module `FreeAbelianGroup A`. -/
noncomputable def FreeAbelianGroup.basis (α : Type*) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

/-- Isomorphic free abelian groups (as modules) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupLinearEquiv (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupEquiv (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) : α ≃ β :=
  .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

/-- Isomorphic free groups have equivalent bases. -/
def Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

/-- Isomorphic free groups have equivalent bases (`IsFreeGroup` variant). -/
def Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H) :
    Generators G ≃ Generators H :=
  .ofFreeGroupEquiv <| (toFreeGroup G).symm.trans <| e.trans <| toFreeGroup H
