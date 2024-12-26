/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty

/-!
# The transfinite iteration of a successor structure

Given a successor structure `Φ : SuccStruct C` (see the file `SmallObject.Iteration.Basic`)
and a well-ordered type `J`, we define the iteration `Φ.iteration J : C`. It is
defined as the colimit of a functor `Φ.iterationFunctor J : J ⥤ C`.

-/

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape C J]

variable {J} in
/-- Given `Φ : SuccStruct C` and an element `j : J` in a well-ordered type,
this is the unique element in `Φ.Iteration j`. -/
noncomputable def iter (j : J) : Φ.Iteration j := Classical.arbitrary _

/-- Given `Φ : SuccStruct C` and a well-ordered type `J`, this
is the functor `J ⥤ C` which gives the iterations of `Φ` indexed by `J`. -/
@[simps (config := .lemmasOnly)]
noncomputable def iterationFunctor : J ⥤ C where
  obj j := (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

/-- Given `Φ : SuccStruct C` and a well-ordered type `J`,
this is an object of `C` which is the iteration of `Φ` to the power `J`:
it is defined as the colimit of the functor `Φ.iterationFunctor J`. -/
noncomputable def iteration : C := colimit (Φ.iterationFunctor J)

/-- The colimit cocone expressing that `Φ.iteration J` is the colimit
of `Φ.iterationFunctor J`. -/
noncomputable def iterationCocone : Cocone (Φ.iterationFunctor J) :=
  colimit.cocone _

@[simp]
lemma iterationCocone_pt : (Φ.iterationCocone J).pt = Φ.iteration J := rfl

/-- `Φ.iteration J` identifies to the colimit of `Φ.iterationFunctor J`. -/
noncomputable def isColimitIterationCocone : IsColimit (Φ.iterationCocone J) :=
  colimit.isColimit _

end CategoryTheory.SmallObject.SuccStruct
