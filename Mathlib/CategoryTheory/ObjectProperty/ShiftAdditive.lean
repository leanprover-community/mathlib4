/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Properties of objects on preadditive categories equipped with shift

In this file, we show that if `C` is a preadditive category
equipped with a shift by an additive monoid `A`, and
`P : ObjectProperty C` is stable under the shift,
then the shift functors on the full subcategory associated
to `P` are additive if the shift functors on `C` are.

This instance is put in a separate file in order to reduce imports.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory.ObjectProperty

instance {C : Type*} [Category* C] (P : ObjectProperty C)
    {A : Type*} [AddMonoid A] [HasShift C A]
    [P.IsStableUnderShift A] [Preadditive C] (n : A)
    [(shiftFunctor C n).Additive] :
    (shiftFunctor P.FullSubcategory n).Additive := by
  have := Functor.additive_of_iso (P.ι.commShiftIso n).symm
  apply Functor.additive_of_comp_faithful _ P.ι

end CategoryTheory.ObjectProperty
