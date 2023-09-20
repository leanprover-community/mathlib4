/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Functor

#align_import category_theory.bicategory.single_obj from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Promoting a monoidal category to a single object bicategory.

A monoidal category can be thought of as a bicategory with a single object.

The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.

We verify that the endomorphisms of that single object recovers the original monoidal category.

One could go much further: the bicategory of monoidal categories
(equipped with monoidal functors and monoidal natural transformations)
is equivalent to the bicategory consisting of
* single object bicategories,
* pseudofunctors, and
* (oplax) natural transformations `η` such that `η.app PUnit.unit = 𝟙 _`.
-/


namespace CategoryTheory

variable (C : Type*) [Category C] [MonoidalCategory C]

/-- Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unusedArguments]
def MonoidalSingleObj (C : Type*) [Category C] [MonoidalCategory C] :=
  PUnit --deriving Inhabited
#align category_theory.monoidal_single_obj CategoryTheory.MonoidalSingleObj

-- Porting note: `deriving` didn't work. Create this instance manually.
instance : Inhabited (MonoidalSingleObj C) := by
  unfold MonoidalSingleObj
  infer_instance

open MonoidalCategory

instance : Bicategory (MonoidalSingleObj C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X Y Z f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := λ_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange

namespace MonoidalSingleObj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unusedArguments]
protected def star : MonoidalSingleObj C :=
  PUnit.unit
#align category_theory.monoidal_single_obj.star CategoryTheory.MonoidalSingleObj.star

/-- The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
def endMonoidalStarFunctor : MonoidalFunctor (EndMonoidal (MonoidalSingleObj.star C)) C where
  obj X := X
  map f := f
  ε := 𝟙 _
  μ X Y := 𝟙 _
#align category_theory.monoidal_single_obj.End_monoidal_star_functor CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctor

/-- The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
noncomputable def endMonoidalStarFunctorIsEquivalence :
    IsEquivalence (endMonoidalStarFunctor C).toFunctor where
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := NatIso.ofComponents fun X => asIso (𝟙 _)
  counitIso := NatIso.ofComponents fun X => asIso (𝟙 _)
#align category_theory.monoidal_single_obj.End_monoidal_star_functor_is_equivalence CategoryTheory.MonoidalSingleObj.endMonoidalStarFunctorIsEquivalence

end MonoidalSingleObj

end CategoryTheory
