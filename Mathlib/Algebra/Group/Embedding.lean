/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.Group.Defs

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.
-/

assert_not_exists MonoidWithZero DenselyOrdered

variable {G : Type*}

section LeftOrRightCancelSemigroup

/-- If left-multiplication by any element is cancellative, left-multiplication by `g` is an
embedding. -/
@[to_additive (attr := simps)
      /-- If left-addition by any element is cancellative, left-addition by `g` is an
        embedding. -/]
def mulLeftEmbedding [Mul G] [IsLeftCancelMul G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g

/-- If right-multiplication by any element is cancellative, right-multiplication by `g` is an
embedding. -/
@[to_additive (attr := simps)
      /-- If right-addition by any element is cancellative, right-addition by `g` is an
        embedding. -/]
def mulRightEmbedding [Mul G] [IsRightCancelMul G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g

@[to_additive]
theorem mulLeftEmbedding_eq_mulRightEmbedding [CommMagma G] [IsCancelMul G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _

end LeftOrRightCancelSemigroup
