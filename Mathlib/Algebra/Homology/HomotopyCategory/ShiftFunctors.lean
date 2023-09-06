import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Shift.SingleFunctors

universe v' u' v u

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace SingleFunctors

open HomologicalComplex

variable {C}

noncomputable def shiftIsoAppX (n a a' : ℤ) (ha' : n + a = a') (X : C) (i : ℤ) :
  ((single C (ComplexShape.up ℤ) a').obj X)⟦n⟧.X i ≅
    ((single C (ComplexShape.up ℤ) a).obj X).X i :=
  if h : a = i then
    shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) a').obj X) n i a' (by linarith) ≪≫
      singleObjXSelf C (ComplexShape.up ℤ) a' X ≪≫
      (singleObjXSelf C (ComplexShape.up ℤ) a X).symm ≪≫ XIsoOfEq _ h
  else
    { hom := 0
      inv := 0
      hom_inv_id := IsZero.eq_of_tgt (isZeroSingleObjX C (ComplexShape.up ℤ) _ _ _
        (fun h' => h (by linarith))) _ _
      inv_hom_id := IsZero.eq_of_tgt (isZeroSingleObjX C (ComplexShape.up ℤ) _ _ _
        (fun h' => h (by linarith))) _ _ }

variable (C)

noncomputable def shiftIso (n a a' : ℤ) (ha' : n + a = a') :
    (single C (ComplexShape.up ℤ) a' ⋙
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) n ≅
        single C (ComplexShape.up ℤ) a) :=
  NatIso.ofComponents (fun X => Hom.isoOfComponents (shiftIsoAppX n a a' ha' X) (by simp))
    (fun {X Y} f => by
      ext i
      by_cases i = a
      · dsimp [shiftIsoAppX]
        rw [dif_pos (by linarith), dif_pos h, dif_pos h.symm, dif_pos h.symm]
        simp [XIsoOfEq]
      · exact IsZero.eq_of_tgt (isZeroSingleObjX _ _ _ _ _ h) _ _)

end SingleFunctors

/-noncomputable def singleFunctors : SingleFunctors C (CochainComplex C ℤ) ℤ where
  functor n := HomologicalComplex.single _ _ n
  shiftIso := SingleFunctors.shiftIso C
  shiftIso_zero := sorry
  shiftIso_add := sorry-/

end CochainComplex
