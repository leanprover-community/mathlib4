/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.adjunction.over
! leanprover-community/mathlib commit cea27692b3fdeb328a2ddba6aabf181754543184
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Over

/-!
# Adjunctions related to the over category

Construct the left adjoint `star X` to `Over.forget X : Over X ⥤ C`.

## TODO
Show `star X` itself has a left adjoint provided `C` is locally cartesian closed.
-/


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star [HasBinaryProducts C] : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X
#align category_theory.star CategoryTheory.star

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar [HasBinaryProducts C] : Over.forget X ⊣ star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)
#align category_theory.forget_adj_star CategoryTheory.forgetAdjStar

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : IsLeftAdjoint (Over.forget X) :=
  ⟨_, forgetAdjStar X⟩

end CategoryTheory
