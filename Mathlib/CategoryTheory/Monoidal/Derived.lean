/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Monoidal.Pentagon
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp

/-!
# The derived monoidal category structure

-/

namespace CategoryTheory

open MonoidalCategory

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities]

def DerivedMonoidal (_ : C ⥤ D) (_ : MorphismProperty C) := D

instance : Category (DerivedMonoidal L W) := inferInstanceAs (Category D)

def toDerivedMonoidal : C ⥤ DerivedMonoidal L W := L

instance : (toDerivedMonoidal L W).IsLocalization W := by assumption

local notation "L'" => toDerivedMonoidal L W

section

variable [(curriedTensor C ⋙ (whiskeringRight C C
  (DerivedMonoidal L W)).obj (toDerivedMonoidal L W)).HasLeftDerivedFunctor₂ W W]

namespace DerivedMonoidal

noncomputable def bifunctor :
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj (L')).leftDerived₂ (L') (L') W W

noncomputable def counit :
    (((whiskeringLeft₂ D).obj (L')).obj (L')).obj (bifunctor L W) ⟶
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj (L') :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj (L')).leftDerivedCounit₂ L L W W

noncomputable def trifunctor₁₂ : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  bifunctorComp₁₂ (bifunctor L W) (bifunctor L W)

noncomputable def trifunctor₂₃ : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  bifunctorComp₂₃ (bifunctor L W) (bifunctor L W)

noncomputable def counit₁₂ :
  ((((whiskeringLeft₃ D).obj (L')).obj (L')).obj (L')).obj (trifunctor₁₂ L W) ⟶
    (Functor.postcompose₃.obj (L')).obj (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)) :=
  bifunctorComp₁₂Counit (counit L W) (counit L W)

noncomputable def counit₂₃ :
  ((((whiskeringLeft₃ D).obj (L')).obj (L')).obj (L')).obj (trifunctor₂₃ L W) ⟶
    (Functor.postcompose₃.obj (L')).obj (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)) :=
  bifunctorComp₂₃Counit (counit L W) (counit L W)

noncomputable def tensorUnitLeftCounit :
    L' ⋙ (bifunctor L W).obj ((L').obj (𝟙_ C)) ⟶ tensorLeft (𝟙_ C) ⋙ L' :=
  Functor.bifunctorCounit₁ (counit L W) (𝟙_ C)

noncomputable def tensorUnitRightCounit :
    L' ⋙ (bifunctor L W).flip.obj ((L').obj (𝟙_ C)) ⟶ tensorRight (𝟙_ C) ⋙ L' :=
  Functor.bifunctorCounit₂ (counit L W) (𝟙_ C)

instance : (bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W :=
  inferInstanceAs (Functor.IsLeftDerivedFunctor₂ _ (Functor.leftDerivedCounit₂ _ _ _ _ _) _ _)

noncomputable def quadrifunctorLeft : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  trifunctorComp₁₂₃ (trifunctor₁₂ L W) (bifunctor L W)

noncomputable def quadrifunctorRight : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  trifunctorComp₂₃₄ (bifunctor L W) (trifunctor₂₃ L W)

end DerivedMonoidal

end

open DerivedMonoidal in
-- needs an assumption about 4-fold tensors
class Functor.HasDerivedMonoidalCategory : Prop where
  hasLeftDerivedFunctor₂ :
    (curriedTensor C ⋙ (whiskeringRight _ _ _).obj (L')).HasLeftDerivedFunctor₂ W W
  trifunctor₁₂_isLeftDerivedFunctor₃ :
    (trifunctor₁₂ L W).IsLeftDerivedFunctor₃ (counit₁₂ L W) W W W
  trifunctor₂₃_isLeftDerivedFunctor₃ :
    (trifunctor₂₃ L W).IsLeftDerivedFunctor₃ (counit₂₃ L W) W W W
  bifunctorObjUnit_isLeftDerivedFunctor :
    ((bifunctor L W).obj ((L').obj (𝟙_ C))).IsLeftDerivedFunctor (tensorUnitLeftCounit L W) W
  bifunctorFlipObjUnit_isLeftDerivedFunctor :
    ((bifunctor L W).flip.obj ((L').obj (𝟙_ C))).IsLeftDerivedFunctor (tensorUnitRightCounit L W) W

namespace Functor.HasDerivedMonoidalCategory

attribute [instance] hasLeftDerivedFunctor₂
  trifunctor₁₂_isLeftDerivedFunctor₃ trifunctor₂₃_isLeftDerivedFunctor₃
  bifunctorObjUnit_isLeftDerivedFunctor
  bifunctorFlipObjUnit_isLeftDerivedFunctor

end Functor.HasDerivedMonoidalCategory

namespace DerivedMonoidal

variable [L.HasDerivedMonoidalCategory W]

noncomputable def associator :
    trifunctor₁₂ L W ≅ trifunctor₂₃ L W :=
  Functor.leftDerived₃NatIso _ _ (counit₁₂ L W) (counit₂₃ L W) W W W
    ((Functor.postcompose₃.obj L).mapIso (curriedAssociatorNatIso C))

@[simp]
lemma associator_hom_fac_app_app_app (X₁ X₂ X₃ : C) :
    (((associator L W).hom.app ((L').obj X₁)).app ((L').obj X₂)).app ((L').obj X₃) ≫
      (((counit₂₃ L W).app X₁).app X₂).app X₃ =
      (((counit₁₂ L W).app X₁).app X₂).app X₃ ≫ (L').map (α_ X₁ X₂ X₃).hom := by
  apply Functor.leftDerived₃NatTrans_fac_app_app_app

noncomputable def leftUnitor : (bifunctor L W).obj ((L').obj (𝟙_ C)) ≅ 𝟭 _ :=
  Functor.leftDerivedNatIso _ _ (tensorUnitLeftCounit L W) (L').rightUnitor.hom W
    (isoWhiskerRight (leftUnitorNatIso C) (L') ≪≫ (L').leftUnitor)

@[reassoc]
lemma leftUnitor_hom_app (X : C) :
    (leftUnitor L W).hom.app ((L').obj X) =
      ((counit L W).app (𝟙_ C)).app X ≫ (L').map (λ_ X).hom := by
  simpa using Functor.leftDerivedNatTrans_fac_app _ _
      (tensorUnitLeftCounit L W) (L').rightUnitor.hom W
      (whiskerRight (leftUnitorNatIso C).hom (L') ≫ (L').leftUnitor.hom) X

noncomputable def rightUnitor : (bifunctor L W).flip.obj ((L').obj (𝟙_ C)) ≅ 𝟭 _ :=
  Functor.leftDerivedNatIso _ _ (tensorUnitRightCounit L W) (L').rightUnitor.hom W
    (isoWhiskerRight (rightUnitorNatIso C) (L') ≪≫ (L').leftUnitor)

lemma rightUnitor_hom_app (X : C) :
    (rightUnitor L W).hom.app ((L').obj X) =
      ((counit L W).app X).app (𝟙_ C) ≫ (L').map (ρ_ X).hom := by
  simpa using Functor.leftDerivedNatTrans_fac_app
    ((bifunctor L W).flip.obj ((L').obj (𝟙_ C))) (𝟭 _)
    (tensorUnitRightCounit L W) (L').rightUnitor.hom W
      (whiskerRight (rightUnitorNatIso C).hom (L') ≫ (L').leftUnitor.hom) X

lemma triangle :
    NatTrans.Triangle (associator L W).hom ((L').obj (𝟙_ C))
      (leftUnitor L W) (rightUnitor L W) where
  triangle := by
    rw [← cancel_mono (Functor.leftUnitor (bifunctor L W)).hom]
    apply (bifunctor L W).leftDerived₂_ext (counit L W) W W
    ext X₁ X₃
    have h₁ := ((counit L W).app X₁).naturality (λ_ X₃).hom
    have h₂ := associator_hom_fac_app_app_app L W X₁ (𝟙_ C) X₃
    have h₃ := congr_app ((counit L W).naturality (ρ_ X₁).hom) X₃
    dsimp [counit₂₃, counit₁₂] at h₁ h₂ h₃ ⊢
    simp only [Category.assoc] at h₂
    rw [Category.comp_id, Category.comp_id, Category.assoc,
      rightUnitor_hom_app, leftUnitor_hom_app, Functor.map_comp_assoc,
      Functor.map_comp, NatTrans.comp_app_assoc, h₁, reassoc_of% h₂, ← (L').map_comp,
      MonoidalCategory.triangle, h₃]

/-lemma pentagon :
    NatTrans.Pentagon (associator L W).hom where
  natTrans₁₂_comp_natTrans₂₃ := by
    sorry

noncomputable instance : MonoidalCategory (DerivedMonoidal L W) :=
  .ofBifunctor _ _ _ _ _ (pentagon L W) (triangle L W)-/

end DerivedMonoidal

end CategoryTheory
