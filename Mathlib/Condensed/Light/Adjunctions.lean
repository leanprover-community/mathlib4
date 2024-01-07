/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Condensed.Light.Abelian

/-!
# Adjunctions regarding categories of light condensed objects

This file shows that the forgetful functor from light condensed abelian groups to light condensed
sets has a left adjoint, called the free light condensed abelian group on a ligh condensed set.

TODO (Dagur):
* Add free light condensed modules over more general rings.
-/

universe u

open CategoryTheory Limits

/-- The forgetful functor from condensed abelian groups to condensed sets. -/
def LightCondensed.abForget : LightCondAb ⥤ LightCondSet := sheafCompose _ (forget AddCommGroupCat)

/--
The left adjoint to the forgetful functor. The *free condensed abelian group* on a condensed set.
-/
noncomputable
def LightCondensed.freeAb : LightCondSet ⥤ LightCondAb :=
  Sheaf.composeAndSheafify _ AddCommGroupCat.free

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def LightCondensed.setAbAdjunction : freeAb ⊣ abForget := Sheaf.adjunction _ AddCommGroupCat.adj
