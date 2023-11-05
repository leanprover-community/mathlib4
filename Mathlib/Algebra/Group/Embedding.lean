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
#align mul_left_embedding mulLeftEmbedding
#align add_left_embedding addLeftEmbedding
#align add_left_embedding_apply addLeftEmbedding_apply
#align mul_left_embedding_apply mulLeftEmbedding_apply

/-- The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive (attr := simps)
      "The embedding of a right cancellative additive semigroup into itself
         by right translation by a fixed element."]
def mulRightEmbedding {G : Type*} [RightCancelSemigroup G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g
#align mul_right_embedding mulRightEmbedding
#align add_right_embedding addRightEmbedding
#align mul_right_embedding_apply mulRightEmbedding_apply
#align add_right_embedding_apply addRightEmbedding_apply

@[to_additive]
theorem mulLeftEmbedding_eq_mulRightEmbedding {G : Type*} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _
#align mul_left_embedding_eq_mul_right_embedding mulLeftEmbedding_eq_mulRightEmbedding
#align add_left_embedding_eq_add_right_embedding addLeftEmbedding_eq_addRightEmbedding

end LeftOrRightCancelSemigroup
