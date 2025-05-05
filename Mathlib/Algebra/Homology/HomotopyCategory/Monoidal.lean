/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Monoidal.Pentagon
import Mathlib.CategoryTheory.QuotientThree

/-!
# The homotopy category is monoidal

-/

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace HomotopyCategory

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [DecidableEq I]

noncomputable example : MonoidalCategory (HomologicalComplex C c) := inferInstance

namespace MonoidalCategory

variable [∀ (K₁ K₂ : HomologicalComplex C c), HasMapBifunctor K₁ K₂ (curriedTensor C) c]

noncomputable abbrev unit : HomotopyCategory C c :=
  (quotient _ _).obj (𝟙_ _)

noncomputable def bifunctor :
    HomotopyCategory C c ⥤ HomotopyCategory C c ⥤ HomotopyCategory C c :=
  (curriedTensor C).bifunctorMapHomotopyCategory c c c

noncomputable def bifunctorIso :
    (((whiskeringLeft₂ _).obj (quotient C c)).obj (quotient C c)).obj (bifunctor C c ) ≅
      MonoidalCategory.curriedTensor (HomologicalComplex C c) ⋙
        (whiskeringRight _ _ _).obj (quotient C c) := Iso.refl _

@[simp]
lemma bifunctorIso_hom_app_app (K₁ K₂ : HomologicalComplex C c) :
  ((bifunctorIso C c).hom.app K₁).app K₂ = 𝟙 _ := rfl

@[simp]
lemma bifunctorIso_inv_app_app (K₁ K₂ : HomologicalComplex C c) :
  ((bifunctorIso C c).inv.app K₁).app K₂ = 𝟙 _ := rfl

noncomputable def bifunctorComp₁₂Iso :
    ((((whiskeringLeft₃ (HomotopyCategory C c)).obj (quotient C c)).obj
      (quotient C c)).obj (quotient C c)).obj
        (bifunctorComp₁₂ (bifunctor C c) (bifunctor C c)) ≅
    (Functor.postcompose₃.obj (quotient C c)).obj
      (bifunctorComp₁₂ (curriedTensor (HomologicalComplex C c))
        (curriedTensor (HomologicalComplex C c))) :=
  Quotient.bifunctorComp₁₂Iso (bifunctorIso C c) (bifunctorIso C c)

noncomputable def bifunctorComp₂₃Iso :
    ((((whiskeringLeft₃ (HomotopyCategory C c)).obj (quotient C c)).obj
      (quotient C c)).obj (quotient C c)).obj
      (bifunctorComp₂₃ (bifunctor C c) (bifunctor C c)) ≅
    (Functor.postcompose₃.obj (quotient C c)).obj
      (bifunctorComp₂₃ (curriedTensor (HomologicalComplex C c))
        (curriedTensor (HomologicalComplex C c))) :=
  Quotient.bifunctorComp₂₃Iso (bifunctorIso C c) (bifunctorIso C c)

@[simp]
lemma bifunctorComp₁₂Iso_hom_app_app_app (K₁ K₂ K₃ : HomologicalComplex C c) :
    (((bifunctorComp₁₂Iso C c).hom.app K₁).app K₂).app K₃ = 𝟙 _ := by
  dsimp only [bifunctorComp₁₂Iso]
  simp
  erw [comp_id, (bifunctor C c).map_id]
  rfl

@[simp]
lemma bifunctorComp₁₂Iso_inv_app_app_app (K₁ K₂ K₃ : HomologicalComplex C c) :
    (((bifunctorComp₁₂Iso C c).inv.app K₁).app K₂).app K₃ = 𝟙 _ := by
  dsimp only [bifunctorComp₁₂Iso]
  simp
  erw [id_comp, (bifunctor C c).map_id]
  rfl

@[simp]
lemma bifunctorComp₂₃Iso_hom_app_app_app (K₁ K₂ K₃ : HomologicalComplex C c) :
    (((bifunctorComp₂₃Iso C c).hom.app K₁).app K₂).app K₃ = 𝟙 _ := by
  dsimp only [bifunctorComp₂₃Iso]
  simp
  erw [comp_id, ((bifunctor C c).obj _).map_id]
  rfl

@[simp]
lemma bifunctorComp₂₃Iso_inv_app_app_app (K₁ K₂ K₃ : HomologicalComplex C c) :
    (((bifunctorComp₂₃Iso C c).inv.app K₁).app K₂).app K₃ = 𝟙 _ := by
  dsimp only [bifunctorComp₂₃Iso]
  simp
  erw [id_comp, ((bifunctor C c).obj _).map_id]
  rfl

noncomputable def associator :
    bifunctorComp₁₂ (bifunctor C c) (bifunctor C c) ≅
      bifunctorComp₂₃ (bifunctor C c) (bifunctor C c) :=
  Quotient.natIsoLift₃ _ _ _
    (bifunctorComp₁₂Iso C c ≪≫ (Functor.postcompose₃.obj (quotient C c)).mapIso
      (curriedAssociatorNatIso (HomologicalComplex C c)) ≪≫
        (bifunctorComp₂₃Iso C c).symm)

@[simp]
lemma associator_hom_app_app_app (K₁ K₂ K₃ : HomologicalComplex C c) :
    (((associator C c).hom.app ((quotient C c).obj K₁)).app ((quotient C c).obj K₂)).app
      ((quotient C c).obj K₃) =
        (quotient C c).map
          ((((curriedAssociatorNatIso (HomologicalComplex C c)).hom.app K₁).app K₂).app K₃) := by
  dsimp [associator]
  erw [Quotient.natTransLift₃_app_app_app]
  dsimp
  rw [bifunctorComp₁₂Iso_hom_app_app_app, bifunctorComp₂₃Iso_inv_app_app_app]
  dsimp
  rw [comp_id]
  apply Category.id_comp

noncomputable def leftUnitor :
    (bifunctor C c).obj (unit C c) ≅ 𝟭 (HomotopyCategory C c) :=
  Quotient.natIsoLift _
    ((bifunctorIso C c).app (𝟙_ _) ≪≫
    isoWhiskerRight (leftUnitorNatIso (HomologicalComplex C c)) (quotient C c))

@[simp]
lemma leftUnitor_hom_app (K : HomologicalComplex C c) :
    (leftUnitor C c).hom.app ((quotient C c).obj K) = (quotient C c).map (λ_ K).hom := by
  apply id_comp

noncomputable def rightUnitor :
    (bifunctor C c).flip.obj (unit C c) ≅ 𝟭 (HomotopyCategory C c) :=
  Quotient.natIsoLift _
    (((flipFunctor _ _ _).mapIso (bifunctorIso C c)).app (𝟙_ _) ≪≫
      isoWhiskerRight (rightUnitorNatIso (HomologicalComplex C c)) (quotient C c))

@[simp]
lemma rightUnitor_hom_app (K : HomologicalComplex C c) :
    (rightUnitor C c).hom.app ((quotient C c).obj K) = (quotient C c).map (ρ_ K).hom := by
  apply id_comp

lemma triangle :
    NatTrans.Triangle (associator C c).hom (unit C c) (leftUnitor C c) (rightUnitor C c) where
  triangle := by
    ext K L
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
    dsimp
    rw [leftUnitor_hom_app, rightUnitor_hom_app, associator_hom_app_app_app]
    exact (quotient C c).congr_map (CategoryTheory.MonoidalCategory.triangle K L)

/-noncomputable instance : MonoidalCategory (HomotopyCategory C c) :=
  .ofBifunctor (unit C c) (bifunctor C c) (associator C c)
  (leftUnitor C c) (rightUnitor C c) sorry (triangle C c)-/

end MonoidalCategory

end HomotopyCategory
