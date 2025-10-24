/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
/-!

# Light condensed `R`-modules

This file defines light condensed modules over a ring `R`.

## Main results

* Light condensed `R`-modules form an abelian category.

* The forgetful functor from light condensed `R`-modules to light condensed sets has a left
  adjoint, sending a light condensed set to the corresponding *free* light condensed `R`-module.
-/


universe u

open CategoryTheory

variable (R : Type u) [Ring R]

/--
The category of light condensed `R`-modules, defined as sheaves of `R`-modules over
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)

noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from light condensed `R`-modules to light condensed sets. -/
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free light condensed `R`-module* on a light
condensed set.
-/
noncomputable
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The light condensed version of the free-forgetful adjunction. -/
noncomputable
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

/--
The category of light condensed abelian groups, defined as sheaves of abelian groups over
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondMod ℤ

noncomputable example : Abelian LightCondAb := inferInstance

namespace LightCondMod

lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x

end LightCondMod
