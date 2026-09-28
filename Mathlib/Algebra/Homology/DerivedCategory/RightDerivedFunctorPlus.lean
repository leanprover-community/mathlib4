/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.DerivesTriangulated

/-!
# The right derived functor on the bounded below derived category

If `F : C ⥤ D` is an additive functor between abelian categories,
where `C` has enough injectives, we define the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
between the corresponding bounded below derived categories. We define
this derived functor as the derived functor of the functor
`F.mapHomotopyCategoryPlus` induced by `F` on the bounded below
homotopy categories. We take advantage of this definition in order to
show that `F.rightDerivedFunctorPlus` is a triangulated functor.
We also show that `F.rightDerivedFunctorPlus` may also be thought of
as a derived functor of the functor `F.mapCochainComplexPlus`
that `F` induces on the categories of bounded below cochain complexes.

TODO(@joelriou): refactor the definition of `Functor.rightDerived`

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

namespace Functor

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor `DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. -/
@[no_expose]
noncomputable def rightDerivedFunctorPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)

/-- The natural transformation that is part of the data of the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. It is defined here as a derived functor of
`F.mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D`,
postcomposed with `DerivedCategory.Plus.Qh`.
(See `Functor.rightDerivedFunctorPlusUnit` for the similar result regarding
`F.mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D`.) -/
@[no_expose]
noncomputable def rightDerivedFunctorPlusUnith :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)

instance :
    F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnith]
  infer_instance

@[no_expose]
noncomputable instance : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C) ℤ

instance : NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift _ F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C) ℤ

open HomotopyCategory.Plus in
instance : F.rightDerivedFunctorPlus.IsTriangulated :=
  (localizerMorphism_derives _).isTriangulated_of_isRightDerivedFunctor
    F.rightDerivedFunctorPlusUnith

/-- A natural transformation that is part of the data of the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has enough injectives. While the right derived functor was defined using
bounded below homotopy categories, this natural transformation allows to say
that it is also the derived functor of the functor
`F.mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D`,
postcomposed with `DerivedCategory.Plus.Q`. -/
@[no_expose, simps! -isSimp app]
noncomputable def rightDerivedFunctorPlusUnit :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
    DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus :=
  whiskerLeft _ (DerivedCategory.Plus.quotientCompQhIso D).inv ≫
    (associator _ _ _).inv ≫ whiskerRight F.quotientCompMapHomotopyCategoryPlusIso.inv _ ≫
    (associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.Plus.quotient C) F.rightDerivedFunctorPlusUnith ≫
    (associator _ _ _).inv ≫ whiskerRight (DerivedCategory.Plus.quotientCompQhIso C).hom _

instance : NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ := by
  dsimp [rightDerivedFunctorPlusUnit]
  infer_instance

instance (K : CochainComplex.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)) := by
  simp only [F.rightDerivedFunctorPlusUnit_app]
  infer_instance

omit [HasDerivedCategory C] [EnoughInjectives C] in
lemma _root_.CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus :
    (CochainComplex.Plus.localizerMorphism C).Derives
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  rw [HomotopyCategory.Plus.inverseImage_quasiIso_mapCochainComplexPlus_injectiveObjectι] at hf
  dsimp
  exact Localization.inverts _ (CochainComplex.Plus.quasiIso D) _
    (homotopyEquivalences_le_quasiIso _ _ _
      (F.homotopyEquivalences_mapCochainComplexPlus_map _
        ((InjectiveObject.ι C).homotopyEquivalences_mapCochainComplexPlus_map _ hf)))

open CochainComplex.Plus in
instance : F.rightDerivedFunctorPlus.IsRightDerivedFunctor
    F.rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso C) :=
  (localizerMorphism_derives_mapCochainComplexPlus F).isRightDerivedFunctor_of_isIso _
    (by dsimp; infer_instance)

example (X : HomotopyCategory.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

example (K : CochainComplex.Plus (InjectiveObject C)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj K))) := by
  infer_instance

end Functor

namespace NatTrans

open CategoryTheory.Functor

variable [EnoughInjectives C] {F₁ F₂ F₃ : C ⥤ D}
  [F₁.Additive] [F₂.Additive] [F₃.Additive]

/-- The natural transformation `F₁.rightDerivedFunctorPlus ⟶ F₂.rightDerivedFunctorPlus`
induced by a natural transformation `F₁ ⟶ F₂`. -/
@[no_expose]
noncomputable def rightDerivedFunctorPlus (τ : F₁ ⟶ F₂) :
    F₁.rightDerivedFunctorPlus ⟶ F₂.rightDerivedFunctorPlus :=
  rightDerivedNatTrans _ _ F₁.rightDerivedFunctorPlusUnith
    F₂.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C)
      (whiskerRight τ.mapHomotopyCategoryPlus _)

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlus_fach (τ : F₁ ⟶ F₂) :
    F₁.rightDerivedFunctorPlusUnith ≫
      whiskerLeft DerivedCategory.Plus.Qh τ.rightDerivedFunctorPlus =
    whiskerRight τ.mapHomotopyCategoryPlus _ ≫ F₂.rightDerivedFunctorPlusUnith := by
  simp [rightDerivedFunctorPlus]

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlus_fach_app (τ : F₁ ⟶ F₂) (K : HomotopyCategory.Plus C) :
    F₁.rightDerivedFunctorPlusUnith.app K ≫ τ.rightDerivedFunctorPlus.app _ =
      DerivedCategory.Plus.Qh.map (τ.mapHomotopyCategoryPlus.app K) ≫
        F₂.rightDerivedFunctorPlusUnith.app K :=
  congr($(τ.rightDerivedFunctorPlus_fach).app K)

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlus_fac_app (τ : F₁ ⟶ F₂) (K : CochainComplex.Plus C) :
    F₁.rightDerivedFunctorPlusUnit.app K ≫ τ.rightDerivedFunctorPlus.app _ =
      DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K) ≫
        F₂.rightDerivedFunctorPlusUnit.app K := by
  simp only [rightDerivedFunctorPlusUnit_app, comp_obj, Category.assoc, naturality,
    rightDerivedFunctorPlus_fach_app_assoc, naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    NatTrans.mapHomotopyCategoryPlus_app_quotient_obj]

instance (τ : F₁ ⟶ F₂) : τ.rightDerivedFunctorPlus.CommShift ℤ :=
  .of_isRightDerivedFunctor F₁.rightDerivedFunctorPlusUnit F₂.rightDerivedFunctorPlusUnit
    (Functor.whiskerRight τ.mapCochainComplexPlus _) (CochainComplex.Plus.quasiIso C)

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlus_fac (τ : F₁ ⟶ F₂) :
    F₁.rightDerivedFunctorPlusUnit ≫
      whiskerLeft DerivedCategory.Plus.Q τ.rightDerivedFunctorPlus =
    whiskerRight (τ.mapCochainComplexPlus) _ ≫ F₂.rightDerivedFunctorPlusUnit := by
  cat_disch

/-- The additive map from `F₁ ⟶ F₂` to `F₁.rightDerivedFunctorPlus ⟶ F₂.rightDerivedFunctorPlus`
that is given by `NatTrans.rightDerivedFunctorPlus`. -/
@[simps!]
noncomputable def rightDerivedFunctorPlusAddMonoidHom :
    (F₁ ⟶ F₂) →+ (F₁.rightDerivedFunctorPlus ⟶ F₂.rightDerivedFunctorPlus) :=
  AddMonoidHom.mk' rightDerivedFunctorPlus
    (fun τ τ' ↦ rightDerived_ext _ (F₁.rightDerivedFunctorPlusUnit)
      (CochainComplex.Plus.quasiIso C) _ _ _ (by cat_disch))

@[simp]
lemma rightDerivedFunctorPlus_add (τ τ' : F₁ ⟶ F₂) :
    (τ + τ').rightDerivedFunctorPlus = τ.rightDerivedFunctorPlus + τ'.rightDerivedFunctorPlus :=
  rightDerivedFunctorPlusAddMonoidHom.map_add τ τ'

@[simp]
lemma rightDerivedFunctorPlus_sub (τ τ' : F₁ ⟶ F₂) :
    (τ - τ').rightDerivedFunctorPlus = τ.rightDerivedFunctorPlus - τ'.rightDerivedFunctorPlus :=
  rightDerivedFunctorPlusAddMonoidHom.map_sub τ τ'

@[simp]
lemma rightDerivedFunctorPlus_neg (τ : F₁ ⟶ F₂) :
    (-τ).rightDerivedFunctorPlus = -τ.rightDerivedFunctorPlus :=
  rightDerivedFunctorPlusAddMonoidHom.map_neg τ

variable (F₁ F₂) in
@[simp]
lemma rightDerivedFunctorPlus_zero :
    (0 : F₁ ⟶ F₂).rightDerivedFunctorPlus = 0 :=
  rightDerivedFunctorPlusAddMonoidHom.map_zero

variable (F₁) in
@[simp]
lemma rightDerivedFunctorPlus_id :
    NatTrans.rightDerivedFunctorPlus (𝟙 F₁) = 𝟙 _ :=
  rightDerived_ext _ (F₁.rightDerivedFunctorPlusUnit) (CochainComplex.Plus.quasiIso C) _ _ _
    (by cat_disch)

attribute [local simp] mapCochainComplexPlus_comp in
@[reassoc]
lemma rightDerivedFunctorPlus_comp (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    (τ ≫ τ').rightDerivedFunctorPlus =
      τ.rightDerivedFunctorPlus ≫ τ'.rightDerivedFunctorPlus :=
  rightDerived_ext _ (F₁.rightDerivedFunctorPlusUnit) (CochainComplex.Plus.quasiIso C) _ _ _
    (by cat_disch)

end NatTrans

end CategoryTheory
