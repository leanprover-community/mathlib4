import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Shift.Basic

open CategoryTheory

variable (C : Type*) [Category C] [Preadditive C] {I : Type*} (c : ComplexShape C) (A : Type*)
  [AddMonoid A] [HasShift C A] [∀ (a : A), (shiftFunctor C a).Additive]

namespace HomologicalComplex

namespace NaiveShift

@[simps!]
noncomputable def shiftFunctorZero : (shiftFunctor C (0 : A)).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (CategoryTheory.shiftFunctorZero C A) c ≪≫
    Functor.mapHomologicalComplexIdIso C c

variable {A} in
@[simps!]
noncomputable def shiftFunctorAdd (a b : A) :
    (shiftFunctor C (a + b)).mapHomologicalComplex c ≅
      (shiftFunctor C a).mapHomologicalComplex c ⋙
        (shiftFunctor C b).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (CategoryTheory.shiftFunctorAdd C a b) c ≪≫
    Functor.mapHomologicalComplexCompIso _ _ _

attribute [local simp] shiftFunctorAdd_zero_add_hom_app
  shiftFunctorAdd_add_zero_hom_app shiftFunctorAdd_assoc_hom_app shiftFunctorAdd'

noncomputable def shiftMkCore : ShiftMkCore (HomologicalComplex C c) A where
  F := fun a => (shiftFunctor C a).mapHomologicalComplex c
  zero := shiftFunctorZero C c A
  add := shiftFunctorAdd C c

end NaiveShift

noncomputable def naiveShift : HasShift (HomologicalComplex C c) A :=
  hasShiftMk _ _ (NaiveShift.shiftMkCore C c A)

end HomologicalComplex
