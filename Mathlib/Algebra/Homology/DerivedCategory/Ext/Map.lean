/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Induced map between Ext

-/

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The commute of `CochainComplex.singleFunctor` with `F` and `F.mapDerivedCategory`. -/
noncomputable def Functor.mapCochainComplexSingleFunctor (n : ℤ) :
    (CochainComplex.singleFunctor C n) ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F ⋙ (CochainComplex.singleFunctor D n) :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n

section Ext

open Localization

instance [h : HasExt.{w'} D] (X Y : C) : HasSmallLocalizedShiftedHom.{w'}
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ℤ
    (((F ⋙ CochainComplex.singleFunctor D 0).obj X))
    (((F ⋙ CochainComplex.singleFunctor D 0).obj Y)) :=
  h (F.obj X) (F.obj Y)

/-- The map between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExt [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (f : Ext.{w} X Y n) : Ext.{w'} (F.obj X) (F.obj Y) n :=
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y) f

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

instance : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex

lemma Functor.mapExt_eq_shiftedHom_map [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (e : Ext X Y n) : (F.mapExt X Y n e).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  simp only [Ext.hom, Ext.homEquiv, comp_obj]
  apply Eq.trans ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).equiv_smallShiftedHomMap
    DerivedCategory.Q DerivedCategory.Q
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  simp only [comp_obj, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom]
  congr 2
  · simp only [mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
      Iso.refl_trans, Iso.trans_inv, Iso.refl_inv, Category.id_comp, isoWhiskerRight_inv,
      Iso.symm_inv, Category.assoc, isoWhiskerLeft_inv, NatTrans.comp_app, comp_obj, Iso.refl_symm,
      associator_inv_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, Category.comp_id]
    exact (Category.id_comp _).symm
  · congr 1
    simp only [mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
      Iso.refl_symm, Iso.refl_trans, Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom,
      isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, comp_obj, associator_hom_app,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app, Category.id_comp]
    nth_rw 2 [← Category.assoc]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

lemma Functor.mapExt_eq_map [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
  (e : Ext X Y n) : (F.mapExt X Y n e).hom =
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ F.mapDerivedCategory.map e.hom ≫
        (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  nth_rw 2 [← Category.assoc]
  exact F.mapExt_eq_shiftedHom_map X Y n e

end

lemma Functor.mapExt_zero [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n 0 = 0 := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  ext
  simp [F.mapExt_eq_map]

lemma Functor.mapExt_add [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) (f g : Ext.{w} X Y n) :
    F.mapExt X Y n (f + g) = F.mapExt X Y n f + F.mapExt X Y n g := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  ext
  simp [F.mapExt_eq_map, F.mapDerivedCategory.map_add]

/-- The additive homomorphism between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun := F.mapExt X Y n
  map_zero' := F.mapExt_zero X Y n
  map_add' := F.mapExt_add X Y n

@[simp]
lemma Functor.mapExtAddHom_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = F.mapExt X Y n := rfl

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

lemma Functor.mapExtAddHom_linear [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (r : R) (f : Ext.{w} X Y n) : F.mapExt X Y n (r • f) = r • (F.mapExt X Y n f) := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  ext
  simp [F.mapExt_eq_map, F.mapDerivedCategory.map_smul]

/-- Upgrade of `F.mapExtAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapExtLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' := F.mapExtAddHom_linear R X Y n

@[simp]
lemma Functor.mapExtLinearMap_toAddMonoidHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n := rfl

lemma Functor.mapExtLinearMap_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExt X Y n := rfl

end Ext

end CategoryTheory
