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
# Map Between Ext Induced by Exact Functor

In this file, we develope the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

-/

@[expose] public section

universe t t' w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma Functor.mapHomologicalComplex_map_exact {ι : Type*} (c : ComplexShape ι)
    (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) :
    (S.map (F.mapHomologicalComplex c)).Exact := by
  refine (HomologicalComplex.exact_iff_degreewise_exact _).mpr (fun i ↦ ?_)
  have : (F.mapHomologicalComplex c) ⋙ (HomologicalComplex.eval D c i) =
    (HomologicalComplex.eval C c i) ⋙ F := by aesop_cat
  simp_rw [← ShortComplex.map_comp, this, ShortComplex.map_comp]
  exact ((HomologicalComplex.exact_iff_degreewise_exact S).mp hS i).map F

instance {ι : Type*} (c : ComplexShape ι) : PreservesFiniteLimits (F.mapHomologicalComplex c) := by
  have := ((F.mapHomologicalComplex c).exact_tfae.out 1 3).mp
  exact (this (F.mapHomologicalComplex_map_exact c)).1

instance {ι : Type*} (c : ComplexShape ι) :
    PreservesFiniteColimits (F.mapHomologicalComplex c) := by
  have := ((F.mapHomologicalComplex c).exact_tfae.out 1 3).mp
  exact (this (F.mapHomologicalComplex_map_exact c)).2

section

open DerivedCategory

lemma Functor.mapTriangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
    ((shiftFunctor (DerivedCategory D) (1 : ℤ)).map (F.mapDerivedCategoryFactors.inv.app S.X₁)) ≫
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁)) := by
  change F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
    ((shiftFunctor (DerivedCategory D) (1 : ℤ)).mapIso (F.mapDerivedCategoryFactors.app S.X₁)).inv ≫
    ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).app (Q.obj S.X₁)).inv
  rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv, Iso.eq_comp_inv]
  conv_lhs => simp only [comp_obj, ShortComplex.map_X₁, triangleOfSESδ,
    CochainComplex.mappingCone.triangle_obj₁, map_comp, map_inv, Iso.app_hom, Category.assoc,
    ← commShiftIso_comp_hom_app, mapIso_hom]
  rw [NatTrans.shift_app_comm]
  simp only [ShortComplex.map_X₁, triangleOfSESδ]
  rw [commShiftIso_comp_hom_app, IsIso.inv_comp_eq]
  simp only [← Category.assoc]
  change _ ≫ ((Q.commShiftIso (1 : ℤ)).app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    S.X₁)).hom = _ ≫ ((Q.commShiftIso (1 : ℤ)).app ((F.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj S.X₁)).hom
  rw [Iso.cancel_iso_hom_right]
  have eq1 : F.mapDerivedCategory.map (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    F.mapDerivedCategoryFactors.hom.app S.X₃ = F.mapDerivedCategoryFactors.hom.app
    (CochainComplex.mappingCone S.f) ≫ Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (CochainComplex.mappingCone.descShortComplex S)) := by
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp
  have eq2 : F.mapDerivedCategory.map (Q.map (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
    F.mapDerivedCategoryFactors.hom.app ((shiftFunctor (CochainComplex C ℤ) 1).obj S.X₁) =
    F.mapDerivedCategoryFactors.hom.app (CochainComplex.mappingCone S.f) ≫ Q.map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (CochainComplex.mappingCone.triangle S.f).mor₃) := by
    rw [← Functor.comp_map, ← NatIso.naturality_2 F.mapDerivedCategoryFactors]
    simp
  rw [eq1, eq2]
  simp only [Category.assoc]
  change (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone S.f)).hom ≫ _ =
    (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone S.f)).hom ≫ _
  rw [Iso.cancel_iso_hom_left, ← Q.map_comp, CochainComplex.mappingCone.map_δ, ← Category.assoc,
    Q.map_comp]
  congr 1
  rw [IsIso.eq_comp_inv, ← Q.map_comp]
  congr 1
  ext n
  simp [CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.descShortComplex,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    mapHomologicalComplex_map_f, CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl]

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
  erw [map_id, map_id, map_id]
  simp only [Category.id_comp, Category.comp_id]
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
  change _ ≫ triangleOfSESδ h1 ≫ (shiftFunctor (DerivedCategory D) 1).map (Q.map f.τ₁) = _
  rw [triangleOfSESδ_hom h1 h2 f]
  change Q.map ((F.mapCochainComplexSingleFunctor 0).app S.X₃).inv ≫
    Q.map ((F.mapCochainComplexSingleFunctor 0).app S.X₃).hom ≫ _ = _
  rw [← Category.assoc, ← Q.map_comp]
  simp

end

section Ext

open Localization

instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    ((F ⋙ CochainComplex.singleFunctor D 0).obj X)
    ((F ⋙ CochainComplex.singleFunctor D 0).obj Y) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Abelian.Ext.mapExactFunctor [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ}
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

open Functor in
lemma Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this, ← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [Category.comp_id, Category.id_comp, Category.assoc]
    congr 1
    change _ = _ ≫ F.mapDerivedCategory.map (𝟙 _)
    simp
  · congr 1
    dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [map_id, Category.id_comp, NatIso.cancel_natIso_hom_left, comp_obj]
    exact (Category.comp_id _).symm

section

attribute [local simp] Abelian.Ext.mapExactFunctor_hom
attribute [local instance] HasDerivedCategory.standard

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

@[simp]
lemma Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F  = 0 := by
  aesop

@[simp]
lemma Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F  = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

/-- The additive homomorphism between `Ext` induced by `F.mapShiftedHomAddHom`. -/
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
    (r • f).mapExactFunctor F  = r • (f.mapExactFunctor F) := by
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

lemma mapExt_mk₀_eq_mk₀_map [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    (mk₀ f).mapExactFunctor F = mk₀ (F.map f) := by
  simp only [Ext.mapExactFunctor, Functor.comp_obj, Int.cast_ofNat_Int, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl ((CochainComplex.singleFunctor C 0).map f)]
  congr
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom]
  exact NatIso.naturality_1 _ f

lemma mapExactFunctor₀ [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    Ext.mapExactFunctor F (X := X) (Y := Y) = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExt_mk₀_eq_mk₀_map, Ext.homEquiv₀]

lemma mapExt_comp_eq_comp_mapExt [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).mapExactFunctor F = (α.mapExactFunctor F).comp (β.mapExactFunctor F) h := by
  simp only [mapExactFunctor, Functor.comp_obj, comp]
  have h' : b + a = (c : ℤ) := by simp [← h, add_comm]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_comp
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    ((F.mapCochainComplexSingleFunctor 0).app Z) α β h']

attribute [local instance] HasDerivedCategory.standard in
lemma mapExt_extClass_eq_extClass_map [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : hS.extClass.mapExactFunctor F = (hS.map_of_exact F).extClass := by
  ext
  rw [Ext.mapExactFunctor_hom, hS.extClass_hom]
  exact (F.mapShiftedHom_singleδ hS).trans (hS.map_of_exact F).extClass_hom.symm

end Abelian.Ext

end Ext

end CategoryTheory
