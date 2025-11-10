/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Single functors from the homotopy category

Let `C` be a preadditive category with a zero object.
In this file, we put together all the single functors `C ⥤ CochainComplex C ℤ`
along with their compatibilities with shifts into the definition
`CochainComplex.singleFunctors C : SingleFunctors C (CochainComplex C ℤ) ℤ`.
Similarly, we define
`HomotopyCategory.singleFunctors C : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ`.

-/

assert_not_exists TwoSidedIdeal

universe v' u' v u

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

open HomologicalComplex

/-- The collection of all single functors `C ⥤ CochainComplex C ℤ` along with
their compatibilites with shifts. (This definition has purposely no `simps`
attribute, as the generated lemmas would not be very useful.) -/
noncomputable def singleFunctors : SingleFunctors C (CochainComplex C ℤ) ℤ where
  functor n := single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by omega
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsimp [single]
          rw [if_neg h, if_neg (fun h' => h (by omega))])))
    (fun {X Y} f => by
      obtain rfl : a' = a + n := by omega
      ext
      simp [single])
  shiftIso_zero a := by
    ext
    dsimp
    simp only [single, shiftFunctorZero_eq, shiftFunctorZero'_hom_app_f,
      XIsoOfEq, eqToIso.hom]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext
    dsimp
    simp only [shiftFunctorAdd_eq, shiftFunctorAdd'_hom_app_f, XIsoOfEq,
      eqToIso.hom, eqToHom_trans, id_comp]

instance (n : ℤ) : ((singleFunctors C).functor n).Additive := by
  dsimp only [singleFunctors]
  infer_instance

instance (R : Type*) [Ring R] (n : ℤ) [Linear R C] :
    Functor.Linear R ((singleFunctors C).functor n) where
  map_smul f r := by
    dsimp [CochainComplex.singleFunctors, HomologicalComplex.single]
    aesop

/-- The single functor `C ⥤ CochainComplex C ℤ` which sends `X` to the complex
consisting of `X` in degree `n : ℤ` and zero otherwise.
(This is definitionally equal to `HomologicalComplex.single C (up ℤ) n`,
but `singleFunctor C n` is the preferred term when interactions with shifts are relevant.) -/
noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Full :=
  inferInstanceAs (single _ _ _).Full

instance (n : ℤ) : (singleFunctor C n).Faithful :=
  inferInstanceAs (single _ _ _).Faithful

end CochainComplex

namespace HomotopyCategory

/-- The collection of all single functors `C ⥤ HomotopyCategory C (ComplexShape.up ℤ))`
for `n : ℤ` along with their compatibilites with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ :=
  (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

/-- The single functor `C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
which sends `X` to the complex consisting of `X` in degree `n : ℤ` and zero otherwise. -/
noncomputable abbrev singleFunctor (n : ℤ) :
    C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor, singleFunctors, SingleFunctors.postcomp]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQuotientIso`.
@[simp] theorem quotient_obj_singleFunctors_obj (n : ℤ) (X : C) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C n).obj X) =
        (HomotopyCategory.singleFunctor C n).obj X :=
  rfl

instance (R : Type*) [Ring R] [Linear R C] (n : ℤ) :
    Functor.Linear R (HomotopyCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (CochainComplex.singleFunctor C n ⋙
    HomotopyCategory.quotient _ _))

/-- The isomorphism given by the very definition of `singleFunctors C`. -/
noncomputable def singleFunctorsPostcompQuotientIso :
    singleFunctors C ≅
      (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _) :=
  Iso.refl _

/-- `HomotopyCategory.singleFunctor C n` is induced by `CochainComplex.singleFunctor C n`. -/
noncomputable def singleFunctorPostcompQuotientIso (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ quotient _ _ :=
  (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

end HomotopyCategory
