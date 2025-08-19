/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Functor

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
* (oplax) natural transformations `η` such that `η.app Unit.unit = 𝟙 _`.
-/

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unusedArguments]
def MonoidalSingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  Unit
deriving Inhabited

open MonoidalCategory

instance : Bicategory (MonoidalSingleObj C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := λ_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange

namespace MonoidalSingleObj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unusedArguments]
protected def star : MonoidalSingleObj C :=
  Unit.unit

/-- The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
def endMonoidalStarFunctor : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  obj X := X
  map f := f

instance : (endMonoidalStarFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

/-- The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
@[simps]
noncomputable def endMonoidalStarFunctorEquivalence :
    EndMonoidal (MonoidalSingleObj.star C) ≌ C where
  functor := endMonoidalStarFunctor C
  inverse :=
    { obj := fun X ↦ X
      map := fun f ↦ f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance endMonoidalStarFunctor_isEquivalence : (endMonoidalStarFunctor C).IsEquivalence :=
  (endMonoidalStarFunctorEquivalence C).isEquivalence_functor

end MonoidalSingleObj

end CategoryTheory
