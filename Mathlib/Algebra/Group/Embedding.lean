/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Embedding.Basic

#align_import algebra.hom.embedding from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.
-/


variable {R : Type*}

section LeftOrRightCancelSemigroup

/-- The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive (attr := simps)
      "The embedding of a left cancellative additive semigroup into itself
         by left translation by a fixed element." ]
def mulLeftEmbedding {G : Type*} [LeftCancelSemigroup G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g

/-- The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive (attr := simps)
      "The embedding of a right cancellative additive semigroup into itself
         by right translation by a fixed element."]
def mulRightEmbedding {G : Type*} [RightCancelSemigroup G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g

@[to_additive]
theorem mulLeftEmbedding_eq_mulRightEmbedding {G : Type*} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _

end LeftOrRightCancelSemigroup
