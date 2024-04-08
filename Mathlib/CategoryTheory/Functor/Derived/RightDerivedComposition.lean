import Mathlib.CategoryTheory.Functor.Derived.RightDerived

namespace CategoryTheory

open Category

namespace Functor

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
  {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃} (e : F₁₂ ⋙ F₂₃ ≅ F₁₃)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {RF₁₂ : D₁ ⥤ D₂} {RF₂₃ : D₂ ⥤ D₃} {RF₁₃ : D₁ ⥤ D₃}
  (α₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ RF₁₂) [RF₁₂.IsRightDerivedFunctor α₁₂ W₁]
  (α₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ RF₂₃) [RF₂₃.IsRightDerivedFunctor α₂₃ W₂]
  (α₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ RF₁₃) [RF₁₃.IsRightDerivedFunctor α₁₃ W₁]

noncomputable def natTransOfIsRightDerivedFunctorComp :
    RF₁₃ ⟶ RF₁₂ ⋙ RF₂₃ :=
  rightDerivedDesc RF₁₃ α₁₃ W₁ _ (whiskerRight e.inv _ ≫
    (associator _ _ _).hom ≫ whiskerLeft F₁₂ α₂₃ ≫ (associator _ _ _).inv ≫
      whiskerRight α₁₂ RF₂₃ ≫ (associator _ _ _).hom)

@[reassoc (attr := simp)]
lemma comp_natTransOfIsRightDerivedFunctorComp_app (X : C₁) :
    α₁₃.app X ≫ (natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃).app (L₁.obj X) =
      L₃.map (e.inv.app X) ≫ α₂₃.app (F₁₂.obj X) ≫ RF₂₃.map (α₁₂.app X) := by
  simp [natTransOfIsRightDerivedFunctorComp]

lemma isIso_natTransOfIsRightDerivedFunctorComp_app (X : C₁)
    [IsIso (α₁₃.app X)] [IsIso (α₁₂.app X)] [IsIso (α₂₃.app (F₁₂.obj X))] :
    IsIso ((natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃).app (L₁.obj X)) :=
  IsIso.of_isIso_fac_left
    (comp_natTransOfIsRightDerivedFunctorComp_app e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃ X)

end Functor

end CategoryTheory
