/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Order.PartialSups

/-!
# Results about `partialSups` of functions taking values in a `Group`
-/

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

@[to_additive]
lemma partialSups_const_mul [MulLeftMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (c * f ·) i = c * partialSups f i := map_partialSups (OrderIso.mulLeft _) ..

@[to_additive]
lemma partialSups_mul_const [MulRightMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (f · * c) i = partialSups f i * c := map_partialSups (OrderIso.mulRight _) ..
