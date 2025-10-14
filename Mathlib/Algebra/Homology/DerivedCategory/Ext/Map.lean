/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
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

open DerivedCategory in
noncomputable def Functor.mapShiftedHomAddHom
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →+
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n := {
    toFun f := (F.mapDerivedCategorySingleFunctor 0).inv.app X
       ≫ f.map F.mapDerivedCategory ≫ ((shiftFunctor (DerivedCategory D) (n : ℤ)).map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y))
    map_zero' := by simp [ShiftedHom.map]
    map_add' x y := by
      rw [ShiftedHom.map, F.mapDerivedCategory.map_add]
      simp [ShiftedHom.map] }

noncomputable def Functor.mapExtAddHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n :=
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  (Ext.homAddEquiv.symm.toAddMonoidHom.comp (F.mapShiftedHomAddHom X Y n)).comp
    Ext.homAddEquiv.toAddMonoidHom

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

instance [F.Linear R] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] :
    F.mapDerivedCategory.Linear R := by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) R
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).comp DerivedCategory.Qh)
    F.mapDerivedCategory]
  have : Functor.Linear R (F.mapHomotopyCategory (ComplexShape.up ℤ)) := by

    sorry
  infer_instance

open DerivedCategory in
lemma Functor.mapShiftedHomAddHom_linear [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (X Y : C) (n : ℤ) (r : R)
    (x : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)) :
    (F.mapShiftedHomAddHom X Y n) (r • x) = r • ((F.mapShiftedHomAddHom X Y n) x)  := by
  simp only [mapShiftedHomAddHom, Int.cast_ofNat_Int, comp_obj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Linear.comp_smul, ← Linear.smul_comp]
  congr
  simp [ShiftedHom.map, F.mapDerivedCategory.map_smul]

open DerivedCategory in
noncomputable def Functor.mapShiftedHomLinearMap
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (X Y : C) (n : ℤ) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) n →ₗ[R]
    ShiftedHom ((singleFunctor D 0).obj (F.obj X)) ((singleFunctor D 0).obj (F.obj Y)) n where
  __ := F.mapShiftedHomAddHom X Y n
  map_smul' := F.mapShiftedHomAddHom_linear R X Y n

noncomputable def Functor.mapExtLinearMap [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n :=
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  (Ext.homLinearEquiv.symm.toLinearMap.comp (F.mapShiftedHomLinearMap R X Y n)).comp
    Ext.homLinearEquiv.toLinearMap

lemma Functor.mapExtLinearMap_toAddMonoidHom [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n := rfl

end CategoryTheory
