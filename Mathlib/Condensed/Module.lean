/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Condensed.Basic
/-!

# Condensed `R`-modules

This file defines condensed modules over a ring `R`.

## Main results

* Condensed `R`-modules form an abelian category.

* The forgetful functor from condensed `R`-modules to condensed sets has a left adjoint, sending a
  condensed set to the corresponding *free* condensed `R`-module.
-/

@[expose] public section

universe u

open CategoryTheory

variable (R : Type (u + 1)) [Ring R]

/--
The category of condensed `R`-modules, defined as sheaves of `R`-modules over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedMod := Condensed.{u} (ModuleCat.{u + 1} R)

noncomputable instance : Abelian (CondensedMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from condensed `R`-modules to condensed sets. -/
def Condensed.forget : CondensedMod R ⥤ CondensedSet := sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free condensed `R`-module* on a condensed set.
-/
noncomputable
def Condensed.free : CondensedSet ⥤ CondensedMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def Condensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

/--
The category of condensed abelian groups is defined as condensed `ℤ`-modules.
-/
abbrev CondensedAb := CondensedMod.{u} (ULift ℤ)

noncomputable example : Abelian CondensedAb.{u} := inferInstance

/-- The forgetful functor from condensed abelian groups to condensed sets. -/
abbrev Condensed.abForget : CondensedAb ⥤ CondensedSet := forget _

/-- The free condensed abelian group on a condensed set. -/
noncomputable abbrev Condensed.freeAb : CondensedSet ⥤ CondensedAb := free _

/-- The free-forgetful adjunction for condensed abelian groups. -/
noncomputable abbrev Condensed.setAbAdjunction : freeAb ⊣ abForget := freeForgetAdjunction _

namespace CondensedMod

lemma hom_naturality_apply {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x

end CondensedMod
