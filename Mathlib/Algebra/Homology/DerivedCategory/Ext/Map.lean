/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Induced map between Ext

-/

universe u u' v v' w w'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section ShiftedHom

open DerivedCategory in
/-- The map between `ShiftedHom` induced by `F.mapDerivedCategory` where `F` is exact. -/
noncomputable def Functor.mapShiftedHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n :=
  fun f ↦ (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    f.map F.mapDerivedCategory ≫ ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧'

lemma Functor.mapShiftedHom_zero [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (X Y : C) (n : ℤ) : F.mapShiftedHom X Y n 0 = 0 := by simp [mapShiftedHom, ShiftedHom.map]

open DerivedCategory in
lemma Functor.mapShiftedHom_add [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C)
    (n : ℤ) (x y : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n) :
    F.mapShiftedHom X Y n (x + y) = F.mapShiftedHom X Y n x + F.mapShiftedHom X Y n y := by
  rw [mapShiftedHom, ShiftedHom.map, F.mapDerivedCategory.map_add]
  simp [mapShiftedHom, ShiftedHom.map]

open DerivedCategory in
/-- The additive homomorphism between `ShiftedHom` induced by
`F.mapDerivedCategory` where `F` is exact. -/
noncomputable def Functor.mapShiftedHomAddHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →+
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n := {
  toFun := F.mapShiftedHom X Y n
  map_zero' := F.mapShiftedHom_zero ..
  map_add' _ _ := F.mapShiftedHom_add .. }

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

instance [F.Linear R] : Functor.Linear R (F.mapHomotopyCategory (ComplexShape.up ℤ)) where
  map_smul {X Y} f r:= by
    dsimp only [Functor.mapHomotopyCategory]
    have full : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).Full := Quotient.full_functor _
    rcases full.1 f with ⟨g, hg⟩
    rw [← hg, ← Functor.Linear.map_smul]
    simp only [HomotopyCategory.quotient, Quotient.lift_map_functor_map, Functor.comp_map,
      Functor.map_smul]
    rfl

instance [F.Linear R] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] :
    F.mapDerivedCategory.Linear R := by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) R
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).comp DerivedCategory.Qh)
    F.mapDerivedCategory]
  infer_instance

open DerivedCategory in
lemma Functor.mapShiftedHomAddHom_linear [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (X Y : C) (n : ℤ) (r : R)
    (x : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)) :
    (F.mapShiftedHomAddHom X Y n) (r • x) = r • ((F.mapShiftedHomAddHom X Y n) x)  := by
  simp only [mapShiftedHomAddHom, mapShiftedHom, comp_obj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Linear.comp_smul, ← Linear.smul_comp]
  congr
  simp [ShiftedHom.map, F.mapDerivedCategory.map_smul]

open DerivedCategory in
/-- Upgrade of `F.mapShiftedHomAddHom` assuming `F` is linear. -/
noncomputable def Functor.mapShiftedHomLinearMap
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →ₗ[R]
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n where
  __ := F.mapShiftedHomAddHom X Y n
  map_smul' := F.mapShiftedHomAddHom_linear R X Y n

end ShiftedHom

section Ext

open Localization

/-- The commute of `CochainComplex.singleFunctor` with `F` and `F.mapDerivedCategory`. -/
noncomputable def Functor.mapCochainComplexSingleFunctor (n : ℤ) :
    (CochainComplex.singleFunctor C n) ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F ⋙ (CochainComplex.singleFunctor D n) :=
  HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n

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

lemma Functor.mapExt_eq_mapShiftedHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n = Ext.homEquiv.symm ∘ F.mapShiftedHom X Y n ∘ Ext.homEquiv := by
  apply funext
  intro f
  apply Ext.homEquiv.injective
  simp only [mapExt, comp_obj, Function.comp_apply, mapShiftedHom, Equiv.apply_symm_apply]
  simp only [Ext.homEquiv]
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  let _ : NatTrans.CommShift F.mapDerivedCategoryFactors.symm.hom ℤ :=
    NatTrans.CommShift.of_iso_inv F.mapDerivedCategoryFactors ℤ
  apply Eq.trans ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).equiv_smallShiftedHomMap
    DerivedCategory.Q DerivedCategory.Q
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    F.mapDerivedCategory F.mapDerivedCategoryFactors.symm f)
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

lemma Functor.mapExt_eq_mapShiftedHom' [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n = (Ext.homAddEquiv.symm.toAddMonoidHom.comp
      (F.mapShiftedHomAddHom X Y n)).comp Ext.homAddEquiv.toAddMonoidHom :=
  F.mapExt_eq_mapShiftedHom X Y n

end

lemma Functor.mapExt_zero [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExt X Y n 0 = 0 := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExt_eq_mapShiftedHom']

lemma Functor.mapExt_add [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) (f g : Ext.{w} X Y n) :
    F.mapExt X Y n (f + g) = F.mapExt X Y n f + F.mapExt X Y n g := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExt_eq_mapShiftedHom']

/-- The additive homomorphism between `Ext` induced by `F.mapShiftedHomAddHom`. -/
noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n where
  toFun := F.mapExt X Y n
  map_zero' := F.mapExt_zero X Y n
  map_add' := F.mapExt_add X Y n

@[simp]
lemma Functor.mapExtAddHom_coe [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = F.mapExt X Y n := rfl

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtAddHom_eq_mapShiftedHomAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtAddHom X Y n = (Ext.homAddEquiv.symm.toAddMonoidHom.comp
      (F.mapShiftedHomAddHom X Y n)).comp Ext.homAddEquiv.toAddMonoidHom :=
  AddMonoidHom.ext (fun _ ↦ congr_fun (F.mapExt_eq_mapShiftedHom X Y n) _)

end

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtAddHom_eq_mapShiftedHomAddHom' [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
    (n : ℕ) : F.mapExtAddHom X Y n = (Ext.homLinearEquiv.symm.toLinearMap.comp
    (F.mapShiftedHomLinearMap R X Y n)).comp Ext.homLinearEquiv.toLinearMap :=
  F.mapExtAddHom_eq_mapShiftedHomAddHom X Y n

end

lemma Functor.mapExtAddHom_linear [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)
    (r : R) (f : Ext.{w} X Y n) : F.mapExtAddHom X Y n (r • f) = r • (F.mapExtAddHom X Y n f) := by
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  simp [F.mapExtAddHom_eq_mapShiftedHomAddHom' R]

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

section

universe t t'

variable [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]

lemma Functor.mapExtLinearMap_eq_mapShiftedHomLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C)
    (n : ℕ) : F.mapExtLinearMap R X Y n = (Ext.homLinearEquiv.symm.toLinearMap.comp
    (F.mapShiftedHomLinearMap R X Y n)).comp Ext.homLinearEquiv.toLinearMap :=
  LinearMap.ext (fun _ ↦ congr_fun (F.mapExt_eq_mapShiftedHom X Y n) _)

end

namespace Abelian.Ext

lemma mapExt_mk₀_eq_mk₀_map [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} (f : X ⟶ Y) :
    F.mapExt X Y 0 (mk₀ f) = mk₀ (F.map f) := by
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  simp only [Functor.mapExt, Functor.comp_obj, Int.cast_ofNat_Int, mk₀]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_mk₀
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    (0 : ℤ) rfl ((CochainComplex.singleFunctor C 0).map f)]
  congr
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism_functor,
    Functor.mapCochainComplexSingleFunctor, Iso.app_inv, Iso.app_hom]
  exact NatIso.naturality_1 _ f

lemma mapExt_comp_eq_comp_mapExt [HasExt.{w} C] [HasExt.{w'} D] {X Y Z : C} {a b : ℕ}
    (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    F.mapExt X Z c (α.comp β h) = (F.mapExt X Y a α).comp (F.mapExt Y Z b β) h := by
  let _ : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).functor.CommShift ℤ := F.commShiftMapCochainComplex
  simp [Functor.mapExt, comp]
  have h' : b + a = (c : ℤ) := by simp [← h, add_comm]
  rw [(F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).smallShiftedHomMap_comp
    ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
    ((F.mapCochainComplexSingleFunctor 0).app Z) α β h']

lemma mapExt_extClass_eq_extClass_map [HasExt.{w} C] [HasExt.{w'} D] {S : ShortComplex C}
    (hS : S.ShortExact) : F.mapExt S.X₃ S.X₁ 1 hS.extClass = (hS.map_of_exact F).extClass :=
  sorry

end Abelian.Ext

end Ext

end CategoryTheory
