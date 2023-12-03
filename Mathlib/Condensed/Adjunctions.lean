/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Condensed.Abelian

/-!
# Adjunctions regarding categories of condensed objects

This file shows that the forgetful functor from condensed abelian groups to condensed sets has a
left adjoint, called the free condensed abelian group on a condensed set.

TODO (Dagur):
* Add free condensed modules over more general rings.
-/

universe u

open CategoryTheory

/-- The forgetful functor from condensed abelian groups to condensed sets. -/
def Condensed.abForget : CondensedAb ⥤ CondensedSet := sheafCompose _ (forget AddCommGroupCat)

/--
The left adjoint to the forgetful functor. The *free condensed abelian group* on a condensed set.
-/
noncomputable
def Condensed.freeAb : CondensedSet ⥤ CondensedAb :=
  Sheaf.composeAndSheafify _ AddCommGroupCat.free

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def Condensed.setAbAdjunction : freeAb ⊣ abForget := Sheaf.adjunction _ AddCommGroupCat.adj
