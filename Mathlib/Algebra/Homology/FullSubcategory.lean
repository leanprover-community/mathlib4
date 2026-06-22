/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Homological complexes in full subcategories

-/

@[expose] public section

open CategoryTheory

namespace HomologicalComplex

/-- Given `P : ObjectProperty V` and `K : HomologicalComplex V c`,
this is a lift of `K` in `HomologicalComplex P.FullSubcategory c`
when `K.X n` satisfies `P` for all `n`. -/
@[simps X d]
def liftObjectProperty {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (K : HomologicalComplex V c) (hK : ∀ (n : ι), P (K.X n)) :
    HomologicalComplex P.FullSubcategory c where
  X n := ⟨_, hK n⟩
  d i j := ObjectProperty.homMk (K.d i j)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `D ⥤ HomologicalComplex P.FullSubcategory c`
which is obtained by lifting a functor `D ⥤ HomologicalComplex V c`
when for any `X : D` and `n`, the objects `(F.obj X).X n`
satisfies a property `P : ObjectProperty V`. -/
@[simps]
def liftFunctorObjectProperty {D : Type*} [Category* D] {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (F : D ⥤ HomologicalComplex V c) (hF : ∀ (X : D) (n : ι), P ((F.obj X).X n)) :
    D ⥤ HomologicalComplex P.FullSubcategory c where
  obj X := liftObjectProperty _ (F.obj X) (hF X)
  map f := { f n := ObjectProperty.homMk ((F.map f).f n) }

end HomologicalComplex
