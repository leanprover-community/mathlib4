/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Condensed.Basic
/-!

Condensed modules form an abelian category.

-/

universe u

open CategoryTheory

/--
The category of condensed `R`-modules, defined as sheaves of `R`-modules over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedMod (R : Type (u+1)) [Ring R] := Condensed.{u} (ModuleCat.{u+1} R)

noncomputable instance (R : Type (u+1)) [Ring R] : Abelian (CondensedMod.{u} R) := sheafIsAbelian
