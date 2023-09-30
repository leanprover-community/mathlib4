import Mathlib.Algebra.Homology.Monoidal

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] {c : ComplexShape I} [DecidableEq I]
  (s : c.TensorSigns)

variable [(curryObj (MonoidalCategory.tensor C)).Additive]
  (K L : HomologicalComplex C c)

def tensorBicomplex (K L : HomologicalComplex C c) :
      HomologicalComplex₂ C c c :=
    (((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).obj K).obj L)

instance [h : HasTensor K L] : GradedObject.HasMap (tensorBicomplex K L).toGradedObject (ComplexShape.TensorSigns.totalComplexShape s).π :=
  h

noncomputable def tensorBiComplexTotalIso [HasTensor K L] [HasTensor L K] :
    Monoidal.tensorObj s K L ≅ (tensorBicomplex K L).total s.totalComplexShape := Iso.refl _

--def tensorBicomplexFlipIso : tensorBicomplex K L ≅ (tensorBicomplex L K).flip := sorry

end HomologicalComplex
