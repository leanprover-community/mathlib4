/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Relations between inserters and (co)algebras.

In this file, we show that the category of (co)algebras for a pointed endofunctor is
equivalent to inserter categories. This is used in transfering some general results
about inserters to (co)algebras.

-/

@[expose] public section

namespace CategoryTheory.Endofunctor

variable {C : Type*} [Category* C] (F : C ⥤ C)

namespace Algebra

/-- Given an endofunctor `F : C ⥤ C`, the category `Algebra F` is equivalent to the category
`Inserter F (𝟭 C)`. -/
@[simps!, implicit_reducible]
def equivInserter :
    Algebra F ≌ Inserter F (𝟭 C) where
  functor.obj X :=
    { obj := X.a
      hom := X.str }
  functor.map f :=
    { hom := f.f
      comm := f.h }
  inverse.obj X :=
    { a := X.obj
      str := X.hom }
  inverse.map f :=
    { f := f.hom
      h := f.comm }
  unitIso := .refl _
  counitIso := .refl _

/-- Through the identification `Algebra F ≌ Inserter F (𝟭 C)`, the forgetful functor
`Algebra F ⥤ C` corresponds to the projection `Inserter F (𝟭 C) ⥤ C`. -/
@[simps!]
def equivInserterFunctorCompProj : (equivInserter F).functor ⋙ Inserter.proj _ _ ≅ forget F :=
  NatIso.ofComponents fun _ ↦ .refl _

/-- Through the identification `Algebra F ≌ Inserter F (𝟭 C)`, the forgetful functor
`Algebra F ⥤ C` corresponds to the projection `Inserter F (𝟭 C) ⥤ C`. -/
@[simps!]
def equivInserterInverseCompForget : (equivInserter F).inverse ⋙ forget F ≅ Inserter.proj _ _ :=
  NatIso.ofComponents fun _ ↦ .refl _

end Algebra

namespace Coalgebra

/-- Given an endofunctor `F : C ⥤ C`, the category `Coalgebra F` is equivalent to the category
`Inserter (𝟭 C) F`. -/
@[simps!, implicit_reducible]
def equivInserter :
    Coalgebra F ≌ Inserter (𝟭 C) F where
  functor.obj X :=
    { obj := X.V
      hom := X.str }
  functor.map f :=
    { hom := f.f
      comm := f.h.symm }
  inverse.obj X :=
    { V := X.obj
      str := X.hom }
  inverse.map f :=
    { f := f.hom
      h := f.comm.symm }
  unitIso := .refl _
  counitIso := .refl _

/-- Through the identification `Coalgebra F ≌ Inserter (𝟭 C) F`, the forgetful functor
`Coalgebra F ⥤ C` corresponds to the projection `Inserter (𝟭 C) F ⥤ C`. -/
@[simps!]
def equivInserterFunctorCompProj : (equivInserter F).functor ⋙ Inserter.proj _ _ ≅ forget F :=
  NatIso.ofComponents fun _ ↦ .refl _

/-- Through the identification `Coalgebra F ≌ Inserter (𝟭 C) F`, the forgetful functor
`Coalgebra F ⥤ C` corresponds to the projection `Inserter (𝟭 C) F ⥤ C`. -/
@[simps!]
def equivInserterInverseCompForget : (equivInserter F).inverse ⋙ forget F ≅ Inserter.proj _ _ :=
  NatIso.ofComponents fun _ ↦ .refl _

end Coalgebra

end CategoryTheory.Endofunctor
