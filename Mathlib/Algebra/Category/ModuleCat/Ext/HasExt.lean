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

For `ModuleCat.{v} R`, if assuming `Small.{v} R`, it has enough projectives, thus for any universe
level `w` with `UnivLE.{v, w}`, `HasExt.{w} (ModuleCat.{v} R)`.

-/

@[expose] public section

universe w v u

variable (R : Type u) [CommRing R] [UnivLE.{v, w}]

instance [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)
