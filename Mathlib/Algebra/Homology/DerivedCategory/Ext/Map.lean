/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Map between Ext groups induced by an exact functor

In this file, we define the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

# Main Definition and results

* `CategoryTheory.Abelian.Ext.mapExactFunctor` : The map between `Ext` induced by
  `CategoryTheory.LocalizerMorphism.smallShiftedHomMap`.

* `CategoryTheory.Functor.mapExtAddHom` : Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor`
  into an additive homomorphism.

* `CategoryTheory.Functor.mapExtLinearMap` : Upgrade of `F.mapExtAddHom` assuming `F` is linear.

* `Ext.mapExt_mk₀_eq_mk₀_map` : `Ext.mapExactFunctor` commutes with `Ext.mk₀`

* `Ext.mapExt_comp_eq_comp_mapExt` : `Ext.mapExactFunctor` preserves `Ext.comp`

* `Ext.mapExt_extClass_eq_extClass_map` :
  `Ext.mapExactFunctor` commutes with `ShortComplex.ShortExact.extClass`

-/

@[expose] public section

universe t t' w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
lemma Functor.mapTriangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
    ((shiftFunctor (DerivedCategory D) (1 : ℤ)).map (F.mapDerivedCategoryFactors.inv.app S.X₁)) ≫
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁)) := by
  rw [← Iso.app_inv, ← Iso.app_hom, ← Functor.mapIso_inv, ← Iso.app_inv,
    ← Category.assoc, ← Category.assoc, Iso.eq_comp_inv, Iso.eq_comp_inv]
  simp only [ShortComplex.map_X₁, comp_obj, triangleOfSESδ,
    CochainComplex.mappingCone.triangle_obj₁, map_comp, map_inv, Iso.app_hom, Category.assoc,
    ← commShiftIso_comp_hom_app, mapIso_hom, NatTrans.shift_app_comm, ShortComplex.map_X₃,
    ShortComplex.map_X₂, ShortComplex.map_f, IsIso.inv_comp_eq]
  simp only [commShiftIso_comp_hom_app, ← Category.assoc]
  rw [← (commShiftIso Q 1).app_hom, Iso.cancel_iso_hom_right]
  conv_rhs =>
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp only [comp_obj, comp_map, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  conv_lhs =>
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp only [comp_obj, comp_map, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [← F.mapDerivedCategoryFactors.app_hom, Iso.cancel_iso_hom_left]
  rw [← Q.map_comp, CochainComplex.mappingCone.map_δ, ← Category.assoc, Q.map_comp]
  congr 1
  rw [IsIso.eq_comp_inv, ← Q.map_comp,
    CochainComplex.mappingCone.descShortComplex_mapHomologicalComplex]

set_option backward.isDefEq.respectTransparency false in
lemma Functor.mapShiftedHom_singleδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex C} (hS : S.ShortExact) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
      ShiftedHom.map hS.singleδ F.mapDerivedCategory ≫
        (shiftFunctor (DerivedCategory D) 1).map ((F.mapDerivedCategorySingleFunctor 0).hom.app
          S.X₁) = (hS.map_of_exact F).singleδ := by
  simp only [comp_obj, ShiftedHom.map, ShortComplex.ShortExact.singleδ,
    SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor, mapIso_hom,
    SingleFunctors.evaluation_map, ShortComplex.map_X₁, mapIso_inv, map_comp, Category.assoc,
    commShiftIso_hom_naturality, ShortComplex.map_X₃]
  rw [F.mapTriangleOfSESδ]
  simp only [ShortComplex.map_X₃, comp_obj, ShortComplex.map_X₁, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [singleFunctorsPostcompQIso_hom_hom, NatTrans.id_app, map_id,
    singleFunctorsPostcompQIso_inv_hom, SingleFunctors.postcomp_functor, comp_obj, Category.id_comp]
  simp only [CochainComplex.singleFunctors, map_id, Category.id_comp, Category.comp_id]
  have eq1 : (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
    F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
    S.X₃) = Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app S.X₃) := by
    simp only [comp_obj, mapDerivedCategorySingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X', singleFunctorIsoCompQ,
      isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_inv,
      Iso.refl_inv, Category.id_comp, isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
      isoWhiskerLeft_inv, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
      associator_hom_app, whiskerLeft_app, Category.comp_id, Iso.inv_hom_id_app]
    exact Category.id_comp _
  have eq2 : (F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C (ComplexShape.up ℤ)
    0).obj S.X₁) ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁) =
    Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app S.X₁) := by
    simp only [comp_obj, mapDerivedCategorySingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X', singleFunctorIsoCompQ,
      isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
      associator_hom_app, whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app,
      Category.id_comp]
    --should be able to using `DerivedCategory.Q_obj_single_obj` ?
    erw [Category.id_comp]
    simp only [Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  rw [← (shiftFunctor (DerivedCategory D) 1).map_comp, eq2, ← Category.assoc, eq1]
  generalize_proofs _ _ _ _ _ _ _ h1 _ h2
  let f : ((S.map (CochainComplex.singleFunctor C 0)).map (F.mapHomologicalComplex
    (ComplexShape.up ℤ))) ⟶ (S.map F).map (CochainComplex.singleFunctor D 0) := {
    τ₁ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₁
    τ₂ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₂
    τ₃ := (F.mapCochainComplexSingleFunctor 0).hom.app S.X₃
    comm₁₂ := (NatTrans.naturality _ S.f).symm
    comm₂₃ := (NatTrans.naturality _ S.g).symm }
  rw [triangleOfSESδ_naturality h1 h2 f]
  simp only [comp_obj, ShortComplex.map_X₃, ShortComplex.map_X₁, f, ← Iso.app_hom, ← Iso.app_inv]
  rw [← Category.assoc, ← Q.map_comp, Iso.inv_hom_id, Q.map_id]
  exact Category.id_comp _

end

section Ext

open Localization

instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    ((F ⋙ CochainComplex.singleFunctor D 0).obj X)
    ((F ⋙ CochainComplex.singleFunctor D 0).obj Y) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `LocalizerMorphism.smallShiftedHomMap`. -/
noncomputable def Abelian.Ext.mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ}
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

set_option backward.isDefEq.respectTransparency false in
open Functor in
lemma Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this, ← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [Category.comp_id, Category.id_comp, Category.assoc]
    congr 1
    exact (Category.comp_id _).symm.trans (congr_arg _ (F.mapDerivedCategory.map_id _).symm)
  · congr 1
    dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [map_id, Category.id_comp, NatIso.cancel_natIso_hom_left, comp_obj]
    exact (Category.comp_id _).symm

section

attribute [local simp] Abelian.Ext.mapExactFunctor_hom
attribute [local instance] HasDerivedCategory.standard

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

@[simp]
lemma Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F = 0 := by
  aesop

@[simp]
lemma Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

/-- Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor` into an additive homomorphism. -/
noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun e := e.mapExactFunctor F
  map_zero' := by simp
  map_add' := by simp

@[simp]
lemma Functor.mapExtAddHom_coe : ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F := rfl

lemma Functor.mapExtAddHom_apply (e : Ext X Y n) : F.mapExtAddHom X Y n e = e.mapExactFunctor F :=
  rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

@[simp]
lemma Functor.mapExactFunctor_smul (r : R) (f : Ext.{w} X Y n) :
    (r • f).mapExactFunctor F = r • (f.mapExactFunctor F) := by
  aesop

/-- Upgrade of `F.mapExtAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapExtLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := by simp

@[simp]
lemma Functor.mapExtLinearMap_toAddMonoidHom : F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n :=
  rfl

lemma Functor.mapExtLinearMap_coe : ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F := rfl

lemma Functor.mapExtLinearMap_apply (e : Ext X Y n) :
    F.mapExtLinearMap R X Y n e = e.mapExactFunctor F := rfl

end

namespace Abelian.Ext

set_option backward.isDefEq.respectTransparency false in
lemma mapExactFunctor_mk₀ [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    (mk₀ f).mapExactFunctor F = mk₀ (F.map f) := by
  dsimp [Ext.mapExactFunctor, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl]
  congr
  simpa only [Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom] using NatIso.naturality_1 _ f

lemma mapExactFunctor₀ [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    Ext.mapExactFunctor F (X := X) (Y := Y) = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExactFunctor_mk₀, Ext.homEquiv₀]

lemma mapExactFunctor_comp [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).mapExactFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).smallShiftedHomMap_comp _
    ((F.mapCochainComplexSingleFunctor 0).app Y) _ α β (show b + a = (c : ℤ) by grind)

attribute [local instance] HasDerivedCategory.standard in
lemma mapExactFunctor_extClass [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).extClass := by
  ext
  rw [Ext.mapExactFunctor_hom, hS.extClass_hom]
  exact (F.mapShiftedHom_singleδ hS).trans (hS.map_of_exact F).extClass_hom.symm

end Abelian.Ext

end Ext

end CategoryTheory
