/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Isomorphisms between free groups imply equivalences of their generators
-/

@[expose] public section

noncomputable section

variable {α β G H : Type*}

open IsFreeGroup Module

/-- `A` is a basis of the ℤ-module `FreeAddCommGroup A`. -/
noncomputable def FreeAddCommGroup.basis (α : Type*) : Basis α ℤ (FreeAddCommGroup α) :=
  ⟨(FreeAddCommGroup.equivFinsupp α).toIntLinearEquiv⟩

/-- Isomorphic free abelian groups (as modules) have equivalent bases. -/
def Equiv.ofFreeAddCommGroupLinearEquiv (e : FreeAddCommGroup α ≃ₗ[ℤ] FreeAddCommGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAddCommGroup β) := (FreeAddCommGroup.basis α).map e
  t.indexEquiv <| FreeAddCommGroup.basis _

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def Equiv.ofFreeAddCommGroupEquiv (e : FreeAddCommGroup α ≃+ FreeAddCommGroup β) : α ≃ β :=
  .ofFreeAddCommGroupLinearEquiv e.toIntLinearEquiv

/-- Isomorphic free groups have equivalent bases. -/
def Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  .ofFreeAddCommGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

/-- Isomorphic free groups have equivalent bases (`IsFreeGroup` variant). -/
def Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H) :
    Generators G ≃ Generators H :=
  .ofFreeGroupEquiv <| (toFreeGroup G).symm.trans <| e.trans <| toFreeGroup H

@[deprecated (since := "2026-11-11")] alias FreeAbelianGroup.basis := FreeAddCommGroup.basis
@[deprecated (since := "2026-11-11")] alias
  Equiv.ofFreeAbelianGroupLinearEquiv := Equiv.ofFreeAddCommGroupLinearEquiv
@[deprecated (since := "2026-11-11")] alias
  Equiv.ofFreeAbelianGroupEquiv := Equiv.ofFreeAddCommGroupEquiv
