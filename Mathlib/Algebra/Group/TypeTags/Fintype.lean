/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Fintype.OfMap

/-!
# Finite types with addition/multiplications

This file contains basic results and instances for finite types that have an
addition/multiplication operator.

## Main results

* `Fintype.decidableEqMulEquivFintype`: `MulEquiv`s on finite types have decidable equality

* `Multiplicative.fintype`: a finite type under addition is also finite under multiplication
-/

assert_not_exists MonoidWithZero MulAction

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset Function

namespace Fintype

section BundledHoms

@[to_additive]
instance decidableEqMulEquivFintype {α β : Type*} [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α ≃* β) :=
  fun a b => decidable_of_iff ((a : α → β) = b) (Injective.eq_iff DFunLike.coe_injective)

end BundledHoms

end Fintype

instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  Fintype.ofEquiv α Additive.ofMul

instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  Fintype.ofEquiv α Multiplicative.ofAdd
