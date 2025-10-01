/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.TransferInstance

@[expose] public section

/-!
# Transfer group with zero structures from `α` to `Shrink α`
-/

noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

instance [SemigroupWithZero α] : SemigroupWithZero (Shrink α) :=
  (equivShrink _).symm.semigroupWithZero
instance [MulZeroClass α] : MulZeroClass (Shrink α) := (equivShrink _).symm.mulZeroClass
instance [MulZeroOneClass α] : MulZeroOneClass (Shrink α) := (equivShrink _).symm.mulZeroOneClass

instance [Monoid M] [AddCommMonoid α] [DistribMulAction M α] : DistribMulAction M (Shrink.{v} α) :=
  (equivShrink α).symm.distribMulAction M
