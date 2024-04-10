import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Shift.SingleFunctors

universe v' u' v u

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex
-- this should be moved (and generalized)

instance {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (n : ι) :
    (HomologicalComplex.single C c n).Additive where
  map_add {X Y} f g := by
    ext
    simp [HomologicalComplex.single]

open HomologicalComplex

variable {C}

lemma singleFunctor_aux (n a a' : ℤ) (ha' : n + a = a') (X : C) (i : ℤ) :
    (((single C (ComplexShape.up ℤ) a').obj X)⟦n⟧).X i =
      ((single C (ComplexShape.up ℤ) a).obj X).X i := by
  dsimp [CategoryTheory.shiftFunctor, shiftMonoidalFunctor, single]
  obtain rfl : a' = a + n := by linarith
  by_cases h : i = a
  · subst h
    simp only [ite_true]
  · rw [if_neg h, if_neg (fun h' => h (by linarith))]

variable (C)

noncomputable def singleFunctors : SingleFunctors C (CochainComplex C ℤ) ℤ where
  functor n := HomologicalComplex.single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => HomologicalComplex.Hom.isoOfComponents
      (fun i => eqToIso (singleFunctor_aux n a a' ha' X i)) (by simp))
    (fun {X Y} f => by
      obtain rfl : a' = a + n := by linarith
      ext
      simp [single])
  shiftIso_zero a := by
    ext
    simp [single, shiftFunctorZero_eq, XIsoOfEq]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext
    simp [single, shiftFunctorAdd_eq, XIsoOfEq]

instance (n : ℤ) : ((singleFunctors C).functor n).Additive := by
  dsimp only [singleFunctors]
  infer_instance

noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

variable {C}

lemma singleFunctors_shiftIso_hom_app_f (n a a' : ℤ) (ha' : n + a = a') (X : C) (i : ℤ) (hi : i = a) :
    (((singleFunctors C).shiftIso n a a' ha').hom.app X).f i =
      (singleObjXIsoOfEq (ComplexShape.up ℤ) a' X (i + n) (by rw [hi, add_comm a, ha'])).hom ≫
        (singleObjXIsoOfEq (ComplexShape.up ℤ) a X i hi).inv := by
  dsimp [singleObjXIsoOfEq, singleFunctors]
  rw [eqToHom_trans]

lemma singleFunctors_shiftIso_inv_app_f (n a a' : ℤ) (ha' : n + a = a') (X : C) (i : ℤ) (hi : i = a) :
    (((singleFunctors C).shiftIso n a a' ha').inv.app X).f i =
        (singleObjXIsoOfEq (ComplexShape.up ℤ) a X i hi).hom ≫
      (singleObjXIsoOfEq (ComplexShape.up ℤ) a' X (i + n) (by rw [hi, add_comm a, ha'])).inv := by
  dsimp [singleObjXIsoOfEq, singleFunctors]
  rw [eqToHom_trans]

end CochainComplex

namespace HomotopyCategory

noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ :=
  (CochainComplex.singleFunctors C).postComp (HomotopyCategory.quotient _ _)

noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor, singleFunctors, SingleFunctors.postComp]
  infer_instance

noncomputable def singleFunctorsPostCompQuotientIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postComp (HomotopyCategory.quotient _ _) :=
  Iso.refl _

noncomputable def singleFunctorPostCompQuotientIso (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ quotient _ _ :=
  (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQuotientIso C)

attribute [irreducible] singleFunctors singleFunctorsPostCompQuotientIso

end HomotopyCategory
