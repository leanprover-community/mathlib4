/-
Copyright (c) 2025 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
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

noncomputable def Functor.mapExt (X Y : C) (n : ℕ) :
    Ext.{w} X Y n → Ext.{w'} (F.obj X) (F.obj Y) n :=
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  Ext.homEquiv.symm ∘ (fun f ↦
    (F.mapDerivedCategoryFactorSingleFunctor 0).symm.hom.app X
       ≫ f.map F.mapDerivedCategory ≫ ((shiftFunctor (DerivedCategory D) (n : ℤ)).map
        ((F.mapDerivedCategoryFactorSingleFunctor 0).hom.app Y))) ∘ Ext.homEquiv

end CategoryTheory
