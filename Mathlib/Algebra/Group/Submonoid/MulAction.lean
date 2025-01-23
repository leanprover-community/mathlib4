/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.SetLike.SMul
import Mathlib.Algebra.Group.Action.Defs

/-!
# Multiplicative actions by submonoids
-/

variable {M α : Type*} [Monoid M] {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

@[to_additive]
instance Submonoid.smul {M' : Type} [MulOneClass M'] [SMul M' α]
    (S : Submonoid M') : SMul (↥S) α := inferInstance

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      "The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. "]
instance mulAction [MulAction M α] : MulAction s α where
  one_smul := one_smul M
  mul_smul r₁ r₂ := mul_smul (r₁ : M) r₂
