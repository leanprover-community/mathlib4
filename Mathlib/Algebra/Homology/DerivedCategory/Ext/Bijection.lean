/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-!

# Bijections Between Ext

In this file, we prove that map between `Ext` induced by fully faithful exact functor with certain
conditions added is bijection.

-/

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section comp

universe u'' v'' w''

variable {E : Type u''} [Category.{v''} E] [Abelian E]

variable (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

instance : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

instance : PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

lemma Functor.mapExt_comp [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E] (X Y : C) (n : ℕ) :
    (F ⋙ G).mapExt X Y n = (G.mapExt (F.obj X) (F.obj Y) n) ∘ (F.mapExt X Y n) := by
  sorry

end comp

variable (h : F.FullyFaithful)

lemma bijective_of_preservesProjectiveObjects [HasExt.{w} C] [HasExt.{w'} D]
    [CategoryTheory.EnoughProjectives C] [F.PreservesProjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExt X Y n) := by
  sorry

lemma bijective_of_preservesInjectiveObjects [HasExt.{w} C] [HasExt.{w'} D]
    [CategoryTheory.EnoughInjectives C] [F.PreservesInjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExt X Y n) := by
  sorry

end CategoryTheory
