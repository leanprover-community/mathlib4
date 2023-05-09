import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.NewHomology

open CategoryTheory Category Preadditive

variable (C : Type _) [Category C] [Preadditive C]

namespace CochainComplex

attribute [local simp] ε_def' zsmul_comp comp_zsmul smul_smul

@[simps!]
def shiftEval (n i i' : ℤ) (hi : i + n = i') :
    (shiftFunctor C n) ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) i ≅
      HomologicalComplex.eval C (ComplexShape.up ℤ) i' :=
  NatIso.ofComponents (fun K => K.XIsoOfEq hi) (by aesop_cat)

@[simps!]
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : i + n = i') (hj : j + n = j') (hk : k + n = k') :
  shiftFunctor C n ⋙ HomologicalComplex.shortComplexFunctor' C _ i j k ≅
    HomologicalComplex.shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.mkIso
    (mulIso ((-1 : Units ℤ)^n) ((shiftEval C n i i' hi).app K))
    ((shiftEval C n j j' hj).app K) (mulIso ((-1 : Units ℤ)^n) ((shiftEval C n k k' hk).app K))
    (by aesop_cat) (by aesop_cat)) (by aesop_cat)

@[simps!]
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : i + n = i') :
  shiftFunctor C n ⋙ HomologicalComplex.shortComplexFunctor C _ i ≅
    HomologicalComplex.shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _ (by simp ; linarith) hi (by simp ; linarith)

section

variable [CategoryWithHomology C] (n i i' : ℤ) (hi : i + n = i')

noncomputable def shiftFunctorHomologyIso :
  shiftFunctor C n ⋙ HomologicalComplex.newHomologyFunctor _ _ i ≅
    HomologicalComplex.newHomologyFunctor _ _ i' :=
  isoWhiskerLeft _ (HomologicalComplex.newHomologyFunctorIso C (ComplexShape.up ℤ) i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftShortComplexFunctorIso C n i i' hi) (ShortComplex.homologyFunctor C) ≪≫
    (HomologicalComplex.newHomologyFunctorIso C (ComplexShape.up ℤ) i').symm

variable {C}

@[simp]
lemma shiftFunctorHomologyIso_hom_app (X : CochainComplex C ℤ) :
    (shiftFunctorHomologyIso C n i i' hi).hom.app X =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n i i' hi).hom.app X) := by
  dsimp [shiftFunctorHomologyIso]
  erw [comp_id, id_comp, id_comp]

@[simp]
lemma shiftFunctorHomologyIso_inv_app (X : CochainComplex C ℤ) :
    (shiftFunctorHomologyIso C n i i' hi).inv.app X =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n i i' hi).inv.app X) := by
  dsimp [shiftFunctorHomologyIso]
  erw [comp_id, id_comp, comp_id]

end

end CochainComplex

namespace HomotopyCategory

noncomputable def shiftFunctorHomologyIso [CategoryWithHomology C] (n i i' : ℤ) (hi : i + n = i') :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙
      newHomologyFunctor C _ i ≅ newHomologyFunctor C _ i' := Quotient.natIsoLift _
  ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (newHomologyFunctorFactors C (ComplexShape.up ℤ) i) ≪≫
    CochainComplex.shiftFunctorHomologyIso C n i i' hi ≪≫
    (newHomologyFunctorFactors C (ComplexShape.up ℤ) i').symm)

end HomotopyCategory
