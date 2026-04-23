/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Condensed.Basic
public import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.Condensed.Explicit
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Category.CompHaus.Limits
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functors from categories of topological spaces to condensed sets

This file defines the embedding of the test objects (compact Hausdorff spaces) into condensed
sets.

## Main definitions

* `compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}` is essentially the yoneda presheaf
  functor. We also define `profiniteToCondensed` and `stoneanToCondensed`.

-/

@[expose] public section

universe u v

open CategoryTheory Limits

section Universes

/-- Increase the size of the target category of condensed sets. -/
def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}

instance : Condensed.ulift.Full := show (sheafCompose _ _).Full from inferInstance

instance : Condensed.ulift.Faithful := show (sheafCompose _ _).Faithful from inferInstance

end Universes

section Topology

/-- The functor from `CompHaus` to `Condensed.{u} (Type u)` given by the Yoneda sheaf. -/
def compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) :=
  (coherentTopology CompHaus).yoneda

/-- The yoneda presheaf as an actual condensed set. -/
def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} :=
  compHausToCondensed' ⋙ Condensed.ulift

/-- Dot notation for the value of `compHausToCondensed`. -/
abbrev CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := compHausToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to profinite spaces. -/
def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} :=
  profiniteToCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `profiniteToCondensed`. -/
abbrev Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := profiniteToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to Stonean spaces. -/
def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} :=
  Stonean.toCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `stoneanToCondensed`. -/
abbrev Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := stoneanToCondensed.obj S

instance : compHausToCondensed'.Full :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Full

instance : compHausToCondensed'.Faithful :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful

instance : compHausToCondensed.Full := inferInstanceAs (_ ⋙ _).Full

instance : compHausToCondensed.Faithful := inferInstanceAs (_ ⋙ _).Faithful

instance : PreservesFiniteCoproducts compHausToCondensed.{u} :=
  inferInstanceAs <| PreservesFiniteCoproducts (coherentTopology _).uliftYoneda

end Topology
