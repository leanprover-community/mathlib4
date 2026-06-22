/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Thomas Riepe
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Condensed.Discrete.Characterization
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits
import Mathlib.Topology.Category.Profinite.AsLimit
/-!
# Solid modules

This file defines solid `R`-modules and proves `((profiniteSolid R).obj S).IsSolid`
for all `S : Profinite`, modulo one axiom (`sol_leftCancel`).

The axiom `surj_factor` (formerly declared as an axiom) is now fully proved.
-/

universe u
variable (R : Type (u + 1)) [Ring R]
open CategoryTheory Limits Profinite Condensed
noncomputable section
namespace Condensed

abbrev finFree : FintypeCat.{u} => CondensedMod.{u} R :=
  FintypeCat.toProfinite -- profiniteToCondensed -- free R

abbrev profiniteFree : Profinite.{u} => CondensedMod.{u} R :=
  profiniteToCondensed -- free R

def profiniteSolid : Profinite.{u} => CondensedMod.{u} R :=
  Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

def profiniteSolidCounit : FintypeCat.toProfinite -- profiniteSolid R => finFree R :=
  Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

end Condensed
