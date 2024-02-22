/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.CategoryTheory.Shift.Prod

/-!
# The naive shift on homological complexes

If `C` is a preadditive category equipped with a shift by an additive monoid `A`,
we define a shift `HomologicalComplex.naiveShift C c A` on the category
`HomologicalComplex C c`.

In particular, if `c = ComplexShape.up ℤ`, the category `HomologicalComplex C c A`
has both a shift by `ℤ` and a shift by `A` which commute, which allows the
definition (which is an instance) of a shift by `ℤ × A`. In particular,
the category `HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)`
is equipped with a shift by `ℤ × ℤ`.

-/

open CategoryTheory

variable (C : Type*) [Category C] [Preadditive C] {I : Type*} (c : ComplexShape I) (A : Type*)
  [AddMonoid A] [HasShift C A] [∀ (a : A), (shiftFunctor C a).Additive]

namespace HomologicalComplex

namespace NaiveShift

/-- The functor `HomologicalComplex C c ⥤ HomologicalComplex C c` induced by
the shift by `0 : A` on `C` identifies to the identity functor.  -/
@[simps!]
noncomputable def shiftFunctorZero : (shiftFunctor C (0 : A)).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (CategoryTheory.shiftFunctorZero C A) c ≪≫
    Functor.mapHomologicalComplexIdIso C c

variable {A} in
/-- The functor `HomologicalComplex C c ⥤ HomologicalComplex C c` induced by
the composition of the shifts by `a` and `b` on `C` identifies to the composition
of the functors induced by the shifts by `a` and by `b`.  -/
@[simps!]
noncomputable def shiftFunctorAdd (a b : A) :
    (shiftFunctor C (a + b)).mapHomologicalComplex c ≅
      (shiftFunctor C a).mapHomologicalComplex c ⋙
        (shiftFunctor C b).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (CategoryTheory.shiftFunctorAdd C a b) c ≪≫
    Functor.mapHomologicalComplexCompIso _ _ _

attribute [local simp] shiftFunctorAdd_zero_add_hom_app
  shiftFunctorAdd_add_zero_hom_app shiftFunctorAdd_assoc_hom_app shiftFunctorAdd'

/-- The data and properties which enables the definition of a shift by `A` on
the category `HomologicalComplex C c` when C has a shift by `A`. -/
@[simps]
noncomputable def shiftMkCore : ShiftMkCore (HomologicalComplex C c) A where
  F := fun a => (shiftFunctor C a).mapHomologicalComplex c
  zero := shiftFunctorZero C c A
  add := shiftFunctorAdd C c

end NaiveShift

/-- The naive shift by `A` on the category `HomologicalComplex C c`
when `C` has a shift by `A`. -/
noncomputable def naiveShift : HasShift (HomologicalComplex C c) A :=
  hasShiftMk _ _ (NaiveShift.shiftMkCore C c A)

section

variable {C c A}
variable {K L : HomologicalComplex C c} (f : K ⟶ L)

variable (K) in
@[simp]
lemma naiveShiftFunctor_obj_X (a : A) (i : I) :
    letI := naiveShift C c A
    ((shiftFunctor _ a).obj K).X i = (shiftFunctor C a).obj (K.X i) := rfl

@[simp]
lemma naiveShiftFunctor_map_f (f : K ⟶ L) (a : A) (i : I) :
    letI := naiveShift C c A
    ((shiftFunctor (HomologicalComplex C c) a).map f).f i = (shiftFunctor C a).map (f.f i) := rfl

variable (K A)

@[simp]
lemma naiveShiftZero_hom_app_f (i : I)  :
    letI := naiveShift C c A
    ((shiftFunctorZero _ A).hom.app K).f i = (shiftFunctorZero C A).hom.app (K.X i) := by
  simp [ShiftMkCore.shiftFunctorZero_eq]

@[simp]
lemma naiveShiftZero_inv_app_f (i : I) :
    letI := naiveShift C c A
    ((shiftFunctorZero _ A).inv.app K).f i = (shiftFunctorZero C A).inv.app (K.X i) := by
  simp [ShiftMkCore.shiftFunctorZero_eq]

variable {A}

@[simp]
lemma naiveShiftAdd_hom_app_f (a b : A) (i : I) :
    letI := naiveShift C c A
    ((shiftFunctorAdd _ a b).hom.app K).f i = (shiftFunctorAdd C a b).hom.app (K.X i) := by
  simp [ShiftMkCore.shiftFunctorAdd_eq]

@[simp]
lemma naiveShiftAdd_inv_app_f (a b : A) (i : I) :
    letI := naiveShift C c A
    ((shiftFunctorAdd _ a b).inv.app K).f i = (shiftFunctorAdd C a b).inv.app (K.X i) := by
  simp [ShiftMkCore.shiftFunctorAdd_eq]

end

variable {A} in
/-- Assuming `C` has a shift by `A`, the naive shift by `a : A` on `CochainComplex C ℤ`
commutes with the shift by `n : ℤ`. -/
@[simps!]
def naiveShiftCommIso (n : ℤ) (a : A) :
    (shiftFunctor C a).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ shiftFunctor _ n ≅
      shiftFunctor _ n ⋙ (shiftFunctor C a).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _))

attribute [local simp] CochainComplex.shiftFunctorZero_hom_app_f
  CochainComplex.shiftFunctorZero_inv_app_f CochainComplex.shiftFunctorAdd_inv_app_f
  CochainComplex.shiftFunctorAdd_hom_app_f XIsoOfEq eqToHom_map

set_option maxHeartbeats 800000 in
instance : ShiftsComm' (CochainComplex C ℤ)
  (inferInstance : HasShift _ ℤ) (naiveShift C (ComplexShape.up ℤ) A) := by
  letI := naiveShift C (ComplexShape.up ℤ) A
  exact { commIso := fun n a => naiveShiftCommIso C n a }

noncomputable instance : HasShift (CochainComplex C ℤ) (ℤ × A) := by
  letI := naiveShift C (ComplexShape.up ℤ) A
  exact HasShift.prod (HomologicalComplex C (ComplexShape.up ℤ)) ℤ A

noncomputable example :
    HasShift (HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (ℤ × ℤ) :=
  inferInstance

end HomologicalComplex
