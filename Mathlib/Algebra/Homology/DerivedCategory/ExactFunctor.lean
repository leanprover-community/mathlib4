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
We study some of the pseudofunctorial properties of this construction,
but we do not define the pseudofunctor which sends an abelian category
to its derived category (TODO).

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w₁ w₂ w₃

open CategoryTheory Category Limits Localization

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

namespace CategoryTheory

namespace Functor

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

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
    Lifting DerivedCategory.Q
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
    Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

noncomputable instance : F.mapDerivedCategory.CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) ℤ
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

instance : NatTrans.CommShift F.mapDerivedCategoryFactorsh.hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom ℤ)

instance : NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ :=
  NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom ℤ (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

instance :
    NatTrans.CommShift (Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory).hom ℤ := by
  dsimp [Lifting.iso]
  infer_instance

instance : F.mapDerivedCategory.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

instance : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ :=
  inferInstanceAs ((F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ)

/-- `DerivedCategory.singleFunctor` commutes with `F` and `F.mapDerivedCategory`. -/
@[simps! -isSimp]
noncomputable def mapDerivedCategorySingleFunctor (n : ℤ) :
    DerivedCategory.singleFunctor C₁ n ⋙ F.mapDerivedCategory ≅
      F ⋙ DerivedCategory.singleFunctor C₂ n :=
  isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C₁ n) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫ (associator ..).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n) _ ≪≫
        associator .. ≪≫ (isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ C₂ n)).symm

instance (R : Type*) [Ring R] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R C₂]
    [F.Linear R] : F.mapDerivedCategory.Linear R := by
  rw [← functor_linear_iff DerivedCategory.Qh (HomotopyCategory.quasiIso C₁
    (ComplexShape.up ℤ)) R ((F.mapHomotopyCategory (ComplexShape.up ℤ)).comp DerivedCategory.Qh)]
  infer_instance

@[reassoc (attr := simp)]
lemma mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app (X : C₁) :
    dsimp% F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C₁ (.up ℤ) 0).obj X) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app X =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, DerivedCategory.singleFunctorIsoCompQ]

@[reassoc (attr := simp)]
lemma mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app (X : C₁) :
    dsimp% (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C₁ (.up ℤ) 0).obj X) =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ]

noncomputable instance :
    Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (.up ℤ))
      DerivedCategory.Q (𝟭 C₁).mapDerivedCategory where
  iso := (𝟭 C₁).mapDerivedCategoryFactors ≪≫
    isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ _) _ ≪≫ leftUnitor _

instance :
    NatTrans.CommShift (Lifting.iso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (.up ℤ))
      DerivedCategory.Q (𝟭 C₁).mapDerivedCategory).hom ℤ := by
  dsimp [Lifting.iso]
  infer_instance

variable (C₁) in
/-- The functor `DerivedCategory C₁ ⥤ DerivedCategory C₁` induced by the identity
functor of `C₁` identifies to the identity functor of the derived category. -/
@[no_expose]
noncomputable def mapDerivedCategoryIdIso : (𝟭 C₁).mapDerivedCategory ≅ 𝟭 _ :=
  liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
      (Iso.refl (DerivedCategory.Q))

instance : NatTrans.CommShift (mapDerivedCategoryIdIso C₁).hom ℤ :=
  NatTrans.CommShift.liftNatTrans ..

@[reassoc]
lemma mapDerivedCategoryIdIso_hom_app (X : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIdIso C₁).hom.app (DerivedCategory.Q.obj X) =
    (𝟭 C₁).mapDerivedCategoryFactors.hom.app X ≫
    DerivedCategory.Q.map ((mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app X) :=
  (liftNatTrans_app ..).trans (by simp [Lifting.iso])

lemma mapDerivedCategoryIdIso_hom_app_singleFunctor_obj (X : C₁) :
    (mapDerivedCategoryIdIso C₁).hom.app ((DerivedCategory.singleFunctor C₁ 0).obj X) =
    ((𝟭 C₁).mapDerivedCategorySingleFunctor 0).hom.app X:= by
  simp [← DerivedCategory.Q_obj_single_obj, mapDerivedCategoryIdIso_hom_app,
    mapDerivedCategorySingleFunctor_hom_app,
    HomologicalComplex.singleMapHomologicalComplex_id_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app]

lemma mapDerivedCategoryIdIso_inv_app_singleFunctor_obj (X : C₁) :
    (mapDerivedCategoryIdIso C₁).inv.app ((DerivedCategory.singleFunctor C₁ 0).obj X) =
    ((𝟭 C₁).mapDerivedCategorySingleFunctor 0).inv.app X := by
  rw [← cancel_epi ((mapDerivedCategoryIdIso C₁).hom.app _), Iso.hom_inv_id_app,
    mapDerivedCategoryIdIso_hom_app_singleFunctor_obj]
  simp

noncomputable instance :
    Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) where
  iso :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft _ G.mapDerivedCategoryFactors

instance :
    NatTrans.CommShift (Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory)).hom ℤ := by
  dsimp [Lifting.iso]
  infer_instance

/-- If `F` and `G` are exact functors between abelian categories, the composition
of the induced functors on the derived category identifies to the functor
induced by `F ⋙ G`. -/
@[no_expose]
noncomputable def mapDerivedCategoryCompIso :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory :=
  liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      ((F ⋙ G).mapHomologicalComplex _ ⋙ DerivedCategory.Q) _ _
      ((associator _ _ _).symm ≪≫
        isoWhiskerRight (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) _)

instance : NatTrans.CommShift (mapDerivedCategoryCompIso F G).hom ℤ := by
  apply +allowSynthFailures NatTrans.CommShift.liftNatTrans
  dsimp
  infer_instance

lemma mapDerivedCategoryCompIso_hom_app_Q_obj (X : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj X) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj X) ≫
      DerivedCategory.Q.map ((mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app X :=
  (liftNatTrans_app ..).trans (by simp [Lifting.iso])

open HomologicalComplex in
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app
    (X : C₁) (n : ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app ((DerivedCategory.singleFunctor C₁ n).obj X) ≫
    ((F ⋙ G).mapDerivedCategorySingleFunctor n).hom.app X =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor n).hom.app X) ≫
    (G.mapDerivedCategorySingleFunctor n).hom.app (F.obj X) := by
  dsimp
  simp only [← DerivedCategory.Q_obj_single_obj, mapDerivedCategoryCompIso_hom_app_Q_obj,
    mapDerivedCategorySingleFunctor_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, map_id, singleMapHomologicalComplex_comp_hom_app,
    map_comp, DerivedCategory.singleFunctorIsoCompQ_inv_app, id_comp, assoc,
    dsimp% G.mapDerivedCategoryFactors.hom.naturality_assoc
      ((singleMapHomologicalComplex F (.up ℤ) n).hom.app X)]
  simp [← map_comp]

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

end Functor

namespace NatTrans

variable {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : C₁ ⥤ C₂} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation between exact functors between abelian categories
induces a natural transformation between the corresponding induced functors
on the derived categories. -/
noncomputable def mapDerivedCategory (τ : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
      (Functor.whiskerRight (τ.mapHomologicalComplex _) DerivedCategory.Q)

instance (τ : F ⟶ G) : NatTrans.CommShift τ.mapDerivedCategory ℤ :=
  NatTrans.CommShift.liftNatTrans ..

@[reassoc]
lemma mapDerivedCategory_app_Q_obj (τ : F ⟶ G) (X : CochainComplex C₁ ℤ) :
    τ.mapDerivedCategory.app (DerivedCategory.Q.obj X) =
    F.mapDerivedCategoryFactors.hom.app X ≫
      DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app X) ≫
        G.mapDerivedCategoryFactors.inv.app X :=
  liftNatTrans_app ..

@[reassoc]
lemma mapDerivedCategory_app_singleFunctor_obj (τ : F ⟶ G) (X : C₁) (n : ℤ) :
    τ.mapDerivedCategory.app ((DerivedCategory.singleFunctor C₁ n).obj X) =
    (F.mapDerivedCategorySingleFunctor n).hom.app X ≫
      (DerivedCategory.singleFunctor C₂ n).map (τ.app X) ≫
        (G.mapDerivedCategorySingleFunctor n).inv.app X := by
  simp [← DerivedCategory.Q_obj_single_obj, mapDerivedCategory_app_Q_obj,
    Functor.mapDerivedCategorySingleFunctor_hom_app,
    Functor.mapDerivedCategorySingleFunctor_inv_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,
    HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]

end NatTrans

end CategoryTheory
