/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The projective derivability structure

-/

@[expose] public section

universe w₁ w₂

open CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category C] [Abelian C]
  {H : Type*} [Category H]

namespace HomologicalComplex

@[simps X d]
def liftObjectProperty {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (K : HomologicalComplex V c) (hK : ∀ (n : ι), P (K.X n)) :
    HomologicalComplex P.FullSubcategory c where
  X n := ⟨_, hK n⟩
  d i j := ObjectProperty.homMk (K.d i j)

@[simps]
def liftFunctorObjectProperty {D : Type*} [Category* D] {ι : Type*} {c : ComplexShape ι}
    {V : Type*} [Category* V] [Preadditive V] (P : ObjectProperty V)
    (F : D ⥤ HomologicalComplex V c) (hF : ∀ (X : D) (n : ι), P ((F.obj X).X n)) :
    D ⥤ HomologicalComplex P.FullSubcategory c where
  obj X := liftObjectProperty _ (F.obj X) (hF X)
  map f := { f n := ObjectProperty.homMk ((F.map f).f n) }

end HomologicalComplex
