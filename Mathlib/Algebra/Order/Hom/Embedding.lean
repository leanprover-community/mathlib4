/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Embedding.Basic

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.
-/


variable {R : Type _}

section LeftOrRightCancelSemigroup

/-- The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a left cancellative additive semigroup into itself
         by left translation by a fixed element.",
  simps]
def mulLeftEmbedding {G : Type _} [LeftCancelSemigroup G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g
#align mul_left_embedding mulLeftEmbedding

/-- The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
      "The embedding of a right cancellative additive semigroup into itself
         by right translation by a fixed element.",
  simps]
def mulRightEmbedding {G : Type _} [RightCancelSemigroup G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g
#align mul_right_embedding mulRightEmbedding

@[to_additive]
theorem mul_left_embedding_eq_mul_right_embedding {G : Type _} [CancelCommMonoid G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _
#align mul_left_embedding_eq_mul_right_embedding mul_left_embedding_eq_mul_right_embedding

end LeftOrRightCancelSemigroup
