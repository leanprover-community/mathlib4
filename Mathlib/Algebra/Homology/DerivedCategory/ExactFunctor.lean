/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# An exact functor induces a functor on derived categories

In this file, we show that if `F : C₁ ⥤ C₂` is an exact functor between
abelian categories, then there is an induced triangulated functor
`F.mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w₁ w₂ w₃

open CategoryTheory Category Limits

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

namespace CategoryTheory.Functor

/-- The functor `DerivedCategory C₁ ⥤ DerivedCategory C₂` induced
by an exact functor `F : C₁ ⥤ C₂` between abelian categories. -/
noncomputable def mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂ :=
  F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)

/-- The functor `F.mapDerivedCategory` is induced
by `F.mapHomologicalComplex (ComplexShape.up ℤ)`. -/
noncomputable def mapDerivedCategoryFactors :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  F.mapHomologicalComplexUpToQuasiIsoFactors _

@[reassoc]
lemma mapDerivedCategoryFactors_hom_naturality {X Y : CochainComplex C₁ ℤ} (f : X ⟶ Y) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ F.mapDerivedCategoryFactors.hom.app Y =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  F.mapDerivedCategoryFactors.hom.naturality f

noncomputable instance :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactors⟩

/-- The functor `F.mapDerivedCategory` is induced
by `F.mapHomotopyCategory (ComplexShape.up ℤ)`. -/
noncomputable def mapDerivedCategoryFactorsh :
    DerivedCategory.Qh ⋙ F.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh _

lemma mapDerivedCategoryFactorsh_hom_app (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
        (DerivedCategory.quotientCompQhIso C₂).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

noncomputable instance :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

noncomputable instance : F.mapDerivedCategory.CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) ℤ
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

instance : NatTrans.CommShift F.mapDerivedCategoryFactorsh.hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom ℤ)

set_option backward.defeqAttrib.useBackward true in
instance : NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ :=
  NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom ℤ (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

instance : F.mapDerivedCategory.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

instance : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ :=
  inferInstanceAs ((F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ)

/-- `DerivedCategory.singleFunctor` commutes with `F` and `F.mapDerivedCategory`. -/
noncomputable def mapDerivedCategorySingleFunctor (n : ℤ) :
    DerivedCategory.singleFunctor C₁ n ⋙ F.mapDerivedCategory ≅
      F ⋙ DerivedCategory.singleFunctor C₂ n :=
  isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C₁ n) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫ (associator ..).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n) _ ≪≫
        associator .. ≪≫ (isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ C₂ n)).symm

instance (R : Type*) [Ring R] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R C₂]
    [F.Linear R] : F.mapDerivedCategory.Linear R := by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh (HomotopyCategory.quasiIso C₁
    (ComplexShape.up ℤ)) R ((F.mapHomotopyCategory (ComplexShape.up ℤ)).comp DerivedCategory.Qh)]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app (X : C₁) :
    dsimp% F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C₁ (.up ℤ) 0).obj X) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app X =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app (X : C₁) :
    dsimp% (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C₁ (.up ℤ) 0).obj X) =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

noncomputable instance :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) where
  iso :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft _ G.mapDerivedCategoryFactors

variable (C₁) in
@[no_expose]
noncomputable def mapDerivedCategoryIdIso : (𝟭 C₁).mapDerivedCategory ≅ 𝟭 _ :=
  sorry

instance : NatTrans.CommShift (mapDerivedCategoryIdIso C₁).hom ℤ := sorry

lemma mapDerivedCategoryIdIso_hom_app_singleFunctor_obj (X : C₁) :
    (mapDerivedCategoryIdIso C₁).hom.app ((DerivedCategory.singleFunctor C₁ 0).obj X) =
    ((𝟭 C₁).mapDerivedCategorySingleFunctor 0).hom.app X := by
  sorry

lemma mapDerivedCategoryIdIso_inv_app_singleFunctor_obj (X : C₁) :
    (mapDerivedCategoryIdIso C₁).inv.app ((DerivedCategory.singleFunctor C₁ 0).obj X) =
    ((𝟭 C₁).mapDerivedCategorySingleFunctor 0).inv.app X := by
  rw [← cancel_epi ((mapDerivedCategoryIdIso C₁).hom.app _), Iso.hom_inv_id_app,
    mapDerivedCategoryIdIso_hom_app_singleFunctor_obj]
  simp

@[no_expose]
noncomputable def mapDerivedCategoryCompIso :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      ((F ⋙ G).mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
      (F ⋙ G).mapDerivedCategory
      ((associator _ _ _).symm ≪≫
        isoWhiskerRight (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) _)

lemma mapDerivedCategoryCompIso_hom_app_Q_obj (X : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj X) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj X) ≫
      DerivedCategory.Q.map ((mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app X :=
  (Localization.liftNatTrans_app ..).trans (by simp [Localization.Lifting.iso])

instance : NatTrans.CommShift (mapDerivedCategoryCompIso F G).hom ℤ := sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app (X : C₁) :
    (mapDerivedCategoryCompIso F G).hom.app ((DerivedCategory.singleFunctor C₁ 0).obj X) ≫
    ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app X =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) := by
  have := DerivedCategory.singleFunctorIsoCompQ C₁ 0
  rw [← NatTrans.naturality_1 _ ((DerivedCategory.singleFunctorIsoCompQ C₁ 0).symm.app X)]
  dsimp
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj]
  dsimp [DerivedCategory.singleFunctorIsoCompQ, mapDerivedCategorySingleFunctor]
  simp only [map_id, assoc, id_comp]
  erw [Functor.map_id, Functor.map_id]
  rw [Category.id_comp]
  rw [Category.id_comp]
  erw [Category.comp_id]
  erw [Category.comp_id]
  erw [Category.comp_id]
  simp only [Iso.inv_hom_id_app_assoc, map_comp, assoc]
  congr 1
  -- requires a compatibility of `singleMapHomologicalComplex` with the composition of functors
  sorry

@[reassoc]
lemma mapDerivedCategorySingleFunctor_inv_app_comp_mapDerivedCategoryCompIso_inv_app (X : C₁) :
    ((F ⋙ G).mapDerivedCategorySingleFunctor 0).inv.app X ≫
    (mapDerivedCategoryCompIso F G).inv.app ((DerivedCategory.singleFunctor C₁ 0).obj X) =
    (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) := by
  rw [← cancel_epi ((G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X)),
    ← cancel_epi (G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X))]
  simp [← mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app_assoc,
    ← Functor.map_comp]

end CategoryTheory.Functor
