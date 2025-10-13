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

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

noncomputable def Functor.mapExtAddHom (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w'} (F.obj X) (F.obj Y) n :=
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  (Ext.homAddEquiv.symm.toAddMonoidHom.comp {
    toFun f := (F.mapDerivedCategorySingleFunctor 0).inv.app X
       ≫ f.map F.mapDerivedCategory ≫ ((shiftFunctor (DerivedCategory D) (n : ℤ)).map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y))
    map_zero' := by simp [ShiftedHom.map]
    map_add' x y := by
      rw [ShiftedHom.map, F.mapDerivedCategory.map_add]
      simp [ShiftedHom.map]
  }).comp Ext.homAddEquiv.toAddMonoidHom

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

noncomputable def Functor.mapExtLinearMap (X Y : C) (n : ℕ) :
    Ext.{w} X Y n →ₗ[R] Ext.{w'} (F.obj X) (F.obj Y) n := sorry

lemma Functor.mapExtLinearMap_toAddMonoidHom (X Y : C) (n : ℕ) :
    F.mapExtLinearMap R X Y n = F.mapExtAddHom X Y n := sorry

end CategoryTheory
