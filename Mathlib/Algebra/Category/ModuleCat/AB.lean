/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
/-!

# AB axioms in module categories

This file proves that the category of modules over a ring satisfies Grothendieck's axioms AB5, AB4,
and AB4*. Further, it proves that `R` is a separator in the category of modules over `R`, and
concludes that this category is Grothendieck abelian.
-/

universe u

open CategoryTheory Limits

variable (R : Type u) [Ring R]

instance : AB5 (ModuleCat.{u} R) where
  ofShape J _ _ :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrp)

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _

instance : AB4Star (ModuleCat.{u} R) where
  ofShape J :=
    HasExactLimitsOfShape.domain_of_functor (Discrete J) (forget₂ (ModuleCat R) AddCommGrp.{u})

lemma ModuleCat.isSeparator : IsSeparator (ModuleCat.of R R) := fun X Y f g h ↦ by
  simp only [Set.mem_singleton_iff, forall_eq, ModuleCat.hom_ext_iff, LinearMap.ext_iff] at h
  ext x
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)) 1

instance : HasSeparator (ModuleCat.{u} R) where
  hasSeparator := ⟨ModuleCat.of R R, ModuleCat.isSeparator R⟩

instance : IsGrothendieckAbelian.{u} (ModuleCat.{u} R) where
