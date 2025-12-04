/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!

# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.

-/

@[expose] public section

universe w v u

variable (R : Type u) [CommRing R] [UnivLE.{v, w}]

instance [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)
