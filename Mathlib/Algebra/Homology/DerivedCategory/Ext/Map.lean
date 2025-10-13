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
variable (F : C ⥤ D) [F.Additive] [PreservesLimits F] [PreservesColimits F]

noncomputable def Functor.mapExt (X Y : C) (n : ℕ) :
    Ext.{w} X Y n → Ext.{w'} (F.obj X) (F.obj Y) n := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  refine Ext.homEquiv.symm ∘ (fun f ↦ ?_) ∘ Ext.homEquiv
  convert f.map F.mapDerivedCategory
  · sorry
  · sorry

end CategoryTheory
