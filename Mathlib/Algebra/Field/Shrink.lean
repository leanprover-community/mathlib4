/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer field structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

universe v
variable {α : Type*} [Small.{v} α]

namespace Shrink

instance [NNRatCast α] : NNRatCast (Shrink.{v} α) := (equivShrink α).symm.nnratCast
instance [RatCast α] : RatCast (Shrink.{v} α) := (equivShrink α).symm.ratCast
instance [DivisionRing α] : DivisionRing (Shrink.{v} α) := (equivShrink _).symm.divisionRing
instance [Field α] : Field (Shrink.{v} α) := (equivShrink _).symm.field

end Shrink
