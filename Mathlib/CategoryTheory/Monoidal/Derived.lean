/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Pentagon
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedFour
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The derived monoidal category structure

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities]

@[nolint unusedArguments]
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

@[simps!]
noncomputable def trifunctor₁₂ : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  bifunctorComp₁₂ (bifunctor L W) (bifunctor L W)

@[simps!]
noncomputable def trifunctor₂₃ : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  bifunctorComp₂₃ (bifunctor L W) (bifunctor L W)

noncomputable def counit₁₂ :
  ((((whiskeringLeft₃ D).obj (L')).obj (L')).obj (L')).obj (trifunctor₁₂ L W) ⟶
    (Functor.postcompose₃.obj (L')).obj (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)) :=
  bifunctorComp₁₂Counit (counit L W) (counit L W)

@[simp]
lemma counit₁₂_app (X₁ X₂ X₃ : C) :
    (((counit₁₂ L W).app X₁).app X₂).app X₃ =
      ((bifunctor L W).map (((counit L W).app X₁).app X₂)).app ((L').obj X₃) ≫
        ((counit L W).app (X₁ ⊗ X₂)).app X₃ := by
  rfl

noncomputable def counit₂₃ :
  ((((whiskeringLeft₃ D).obj (L')).obj (L')).obj (L')).obj (trifunctor₂₃ L W) ⟶
    (Functor.postcompose₃.obj (L')).obj (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)) :=
  bifunctorComp₂₃Counit (counit L W) (counit L W)

@[simp]
lemma counit₂₃_app (X₁ X₂ X₃ : C) :
    (((counit₂₃ L W).app X₁).app X₂).app X₃ =
      ((bifunctor L W).obj ((L').obj X₁)).map (((counit L W).app X₂).app X₃) ≫
        ((counit L W).app X₁).app (X₂ ⊗ X₃) := by
  rfl

noncomputable def tensorUnitLeftCounit :
    L' ⋙ (bifunctor L W).obj ((L').obj (𝟙_ C)) ⟶ tensorLeft (𝟙_ C) ⋙ L' :=
  Functor.bifunctorCounit₁ (counit L W) (𝟙_ C)

@[simp]
lemma tensorUnitLeftCounit_app (X : C) :
    (tensorUnitLeftCounit L W).app X = ((counit L W).app (𝟙_ C)).app X := rfl

noncomputable def tensorUnitRightCounit :
    L' ⋙ (bifunctor L W).flip.obj ((L').obj (𝟙_ C)) ⟶ tensorRight (𝟙_ C) ⋙ L' :=
  Functor.bifunctorCounit₂ (counit L W) (𝟙_ C)

@[simp]
lemma tensorUnitRightCounit_app (X : C) :
    (tensorUnitRightCounit L W).app X = ((counit L W).app X).app (𝟙_ C) := rfl

instance : (bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W :=
  inferInstanceAs (Functor.IsLeftDerivedFunctor₂ _ (Functor.leftDerivedCounit₂ _ _ _ _ _) _ _)

noncomputable def quadrifunctorLeft : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  trifunctorComp₁₂₃ (trifunctor₁₂ L W) (bifunctor L W)

noncomputable def quadrifunctorRight : DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  trifunctorComp₂₃₄ (bifunctor L W) (trifunctor₂₃ L W)

noncomputable def quadrifunctorRightCounit :
    (((((whiskeringLeft₄ D).obj (L')).obj (L')).obj (L')).obj (L')).obj
      (quadrifunctorRight L W) ⟶
        (Functor.postcompose₄.obj (L')).obj
          (trifunctorComp₂₃₄ (curriedTensor C)
          (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C))) :=
  trifunctorComp₂₃₄Counit (counit₂₃ L W) (counit L W)

@[simp]
lemma quadrifunctorRightCounit_app_app_app_app (X₁ X₂ X₃ X₄ : C) :
    ((((quadrifunctorRightCounit L W).app X₁).app X₂).app X₃).app X₄ =
  ((bifunctor L W).obj ((L').obj X₁)).map
      (((bifunctor L W).obj ((L').obj X₂)).map (((counit L W).app X₃).app X₄) ≫
        ((counit L W).app X₂).app (X₃ ⊗ X₄)) ≫ ((counit L W).app X₁).app (X₂ ⊗ X₃ ⊗ X₄) :=
  rfl

end DerivedMonoidal

end

open DerivedMonoidal in
class Functor.HasDerivedMonoidalCategory : Prop where
  curriedTensor_hasLeftDerivedFunctor₂ :
    (curriedTensor C ⋙ (whiskeringRight _ _ _).obj (L')).HasLeftDerivedFunctor₂ W W
  trifunctor₁₂_isLeftDerivedFunctor₃ :
    (trifunctor₁₂ L W).IsLeftDerivedFunctor₃ (counit₁₂ L W) W W W
  trifunctor₂₃_isLeftDerivedFunctor₃ :
    (trifunctor₂₃ L W).IsLeftDerivedFunctor₃ (counit₂₃ L W) W W W
  bifunctorObjUnit_isLeftDerivedFunctor :
    ((bifunctor L W).obj ((L').obj (𝟙_ C))).IsLeftDerivedFunctor (tensorUnitLeftCounit L W) W
  bifunctorFlipObjUnit_isLeftDerivedFunctor :
    ((bifunctor L W).flip.obj ((L').obj (𝟙_ C))).IsLeftDerivedFunctor (tensorUnitRightCounit L W) W
  quadrifunctorRight_isLeftDerivedFunctor₄ :
    (quadrifunctorRight L W).IsLeftDerivedFunctor₄ (quadrifunctorRightCounit L W) W W W W

namespace Functor.HasDerivedMonoidalCategory

attribute [instance] curriedTensor_hasLeftDerivedFunctor₂
  trifunctor₁₂_isLeftDerivedFunctor₃ trifunctor₂₃_isLeftDerivedFunctor₃
  bifunctorObjUnit_isLeftDerivedFunctor bifunctorFlipObjUnit_isLeftDerivedFunctor
  quadrifunctorRight_isLeftDerivedFunctor₄

end Functor.HasDerivedMonoidalCategory

namespace DerivedMonoidal

variable [L.HasDerivedMonoidalCategory W]

noncomputable def associator :
    trifunctor₁₂ L W ≅ trifunctor₂₃ L W :=
  Functor.leftDerived₃NatIso _ _ (counit₁₂ L W) (counit₂₃ L W) W W W
    ((Functor.postcompose₃.obj L).mapIso (curriedAssociatorNatIso C))

@[reassoc (attr := simp)]
lemma associator_hom_fac_app_app_app (X₁ X₂ X₃ : C) :
    (((associator L W).hom.app ((L').obj X₁)).app ((L').obj X₂)).app ((L').obj X₃) ≫
      ((bifunctor L W).obj ((L').obj X₁)).map (((counit L W).app X₂).app X₃) ≫
        ((counit L W).app X₁).app (X₂ ⊗ X₃) =
      ((bifunctor L W).map (((counit L W).app X₁).app X₂)).app ((L').obj X₃) ≫
        ((counit L W).app (X₁ ⊗ X₂)).app X₃ ≫ (L').map (α_ X₁ X₂ X₃).hom := by
  dsimp
  conv_rhs => rw [← Category.assoc]
  apply Functor.leftDerived₃NatTrans_fac_app_app_app

noncomputable def leftUnitor : (bifunctor L W).obj ((L').obj (𝟙_ C)) ≅ 𝟭 _ :=
  Functor.leftDerivedNatIso _ _ (tensorUnitLeftCounit L W) (L').rightUnitor.hom W
    (isoWhiskerRight (leftUnitorNatIso C) (L') ≪≫ (L').leftUnitor)

@[reassoc]
lemma leftUnitor_hom_app (X : C) :
    (leftUnitor L W).hom.app ((L').obj X) =
      ((counit L W).app (𝟙_ C)).app X ≫ (L').map (λ_ X).hom := by
  simpa using Functor.leftDerivedNatTrans_app _ _
      (tensorUnitLeftCounit L W) (L').rightUnitor.hom W
      (whiskerRight (leftUnitorNatIso C).hom (L') ≫ (L').leftUnitor.hom) X

noncomputable def rightUnitor : (bifunctor L W).flip.obj ((L').obj (𝟙_ C)) ≅ 𝟭 _ :=
  Functor.leftDerivedNatIso _ _ (tensorUnitRightCounit L W) (L').rightUnitor.hom W
    (isoWhiskerRight (rightUnitorNatIso C) (L') ≪≫ (L').leftUnitor)

lemma rightUnitor_hom_app (X : C) :
    (rightUnitor L W).hom.app ((L').obj X) =
      ((counit L W).app X).app (𝟙_ C) ≫ (L').map (ρ_ X).hom := by
  simpa using Functor.leftDerivedNatTrans_app
    ((bifunctor L W).flip.obj ((L').obj (𝟙_ C))) (𝟭 _)
    (tensorUnitRightCounit L W) (L').rightUnitor.hom W
      (whiskerRight (rightUnitorNatIso C).hom (L') ≫ (L').leftUnitor.hom) X

set_option backward.isDefEq.respectTransparency false in
lemma triangle :
    NatTrans.Triangle (associator L W).hom ((L').obj (𝟙_ C))
      (leftUnitor L W) (rightUnitor L W) where
  triangle := by
    rw [← cancel_mono (Functor.leftUnitor (bifunctor L W)).hom]
    apply (bifunctor L W).leftDerived₂_ext (counit L W) W W
    ext X₁ X₃
    have h₁ := ((counit L W).app X₁).naturality (λ_ X₃).hom
    have h₂ := congr_app ((counit L W).naturality (ρ_ X₁).hom) X₃
    dsimp at h₁ h₂ ⊢
    rw [Category.comp_id, Category.comp_id, Category.assoc,
      rightUnitor_hom_app, leftUnitor_hom_app, Functor.map_comp_assoc,
      Functor.map_comp, NatTrans.comp_app_assoc, h₁,
      associator_hom_fac_app_app_app_assoc,
      Category.assoc, Category.assoc, ← (L').map_comp,
      MonoidalCategory.triangle, h₂]

set_option backward.isDefEq.respectTransparency false in
lemma pentagon :
    NatTrans.Pentagon (associator L W).hom where
  natTrans₁₂_comp_natTrans₂₃_comp_natTrans₃₄ := by
    apply (quadrifunctorRight L W).leftDerived₄_ext (quadrifunctorRightCounit L W) W W W W
    ext X₁ X₂ X₃ X₄
    have h₁ := ((counit L W).app X₁).naturality (α_ X₂ X₃ X₄).hom
    have h₂ := congr_app (((associator L W).hom.app ((L').obj X₁)).naturality
      (((counit L W).app X₂).app X₃)) ((L').obj X₄)
    have h₃ := associator_hom_fac_app_app_app L W X₁ (X₂ ⊗ X₃) X₄
    have h₄ := congr_app ((counit L W).naturality (α_ X₁ X₂ X₃).hom) X₄
    have h₅ := (((associator L W).hom.app ((L').obj X₁)).app ((L').obj X₂)).naturality
      (((counit L W).app X₃).app X₄)
    have h₆ := ((bifunctor L W).map (((counit L W).app X₁).app X₂)).naturality
      (((counit L W).app X₃).app X₄)
    have h₇ := congr_app (congr_app ((associator L W).hom.naturality
      (((counit L W).app X₁).app X₂)) ((L').obj X₃)) ((L').obj X₄)
    dsimp at h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
    conv_lhs =>
      rw [Category.assoc, Category.assoc,
        ← Functor.map_comp_assoc, associator_hom_fac_app_app_app,
        Functor.map_comp_assoc, Functor.map_comp_assoc, h₁, ← reassoc_of% h₂,
        reassoc_of% h₃, ← NatTrans.comp_app_assoc,
        ← NatTrans.comp_app_assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, associator_hom_fac_app_app_app, Functor.map_comp,
        NatTrans.comp_app_assoc, Functor.map_comp, NatTrans.comp_app_assoc,
        reassoc_of% h₄, ← Functor.map_comp, ← Functor.map_comp, MonoidalCategory.pentagon,
        Functor.map_comp]
    conv_rhs =>
      rw [Category.assoc, Functor.map_comp_assoc,
        ← reassoc_of% h₅, associator_hom_fac_app_app_app, reassoc_of% h₆, ← reassoc_of% h₇,
        associator_hom_fac_app_app_app_assoc, Category.assoc, Category.assoc]

noncomputable instance : MonoidalCategory (DerivedMonoidal L W) :=
  .ofBifunctor _ _ _ _ _ (pentagon L W) (triangle L W)

lemma tensorObj_eq (X₁ X₂ : DerivedMonoidal L W) :
    X₁ ⊗ X₂ = ((bifunctor L W).obj X₁).obj X₂ :=
  rfl

lemma whiskerLeft_eq (X₁ : DerivedMonoidal L W) {X₂ Y₂ : DerivedMonoidal L W} (f₂ : X₂ ⟶ Y₂) :
    X₁ ◁ f₂ = ((bifunctor L W).obj X₁).map f₂ := rfl

lemma whiskerRight_eq {X₁ Y₁ : DerivedMonoidal L W} (f₁ : X₁ ⟶ Y₁) (X₂ : DerivedMonoidal L W) :
    f₁ ▷ X₂ = ((bifunctor L W).map f₁).app X₂ := rfl

lemma associator_eq (X₁ X₂ X₃ : DerivedMonoidal L W) :
    α_ X₁ X₂ X₃ = (((associator L W).app X₁).app X₂).app X₃ :=
  rfl

lemma leftUnitor_eq (X : DerivedMonoidal L W) :
    λ_ X = (leftUnitor L W).app X := rfl

lemma rightUnitor_eq (X : DerivedMonoidal L W) :
    ρ_ X = (rightUnitor L W).app X := rfl

attribute [local simp] tensorObj_eq whiskerLeft_eq whiskerRight_eq associator_eq
  leftUnitor_eq rightUnitor_eq leftUnitor_hom_app rightUnitor_hom_app

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (toDerivedMonoidal L W).LaxMonoidal where
  ε := 𝟙 _
  μ X₁ X₂ := ((counit L W).app X₁).app X₂
  μ_natural_right X₁ f₂ := ((counit L W).app X₁).naturality f₂
  μ_natural_left f₁ X₂ := congr_app ((counit L W).naturality f₁) X₂

instance : IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal L W)) :=
  inferInstanceAs (IsIso (𝟙 _))

instance : (curriedTensor (DerivedMonoidal L W)).IsLeftDerivedFunctor₂
    (Functor.LaxMonoidal.μNatTrans (toDerivedMonoidal L W)) W W :=
  inferInstanceAs ((bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W)

end DerivedMonoidal

end CategoryTheory
