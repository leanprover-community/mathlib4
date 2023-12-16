/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CountableInter
/-!
# Compact sets and compact spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof`: a set such that each open cover has a countable subcover. This is defined in mathlib
  using filters.
* `LindelofSpace`: typeclass stating that the whole space is a Lindëlof set.
* `NonLindelofSpace`: a space that is not a Lindëlof space.

## Main results

* ToBeAdded
-/
open Set Filter Topology TopologicalSpace Classical


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

-- compact sets
section Lindelof

/-- A set `s` is Lindelöf if for every nontrivial filter `f` with the countable intersection
  property that contains `s`, there exists `a ∈ s` such that every set of `f`
  meets every neighborhood of `a`. -/
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- Type class for Lindelöf spaces.  -/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)

/-- `X` is a non-Lindelöf topological space if it is not a Lindelöf space. -/
class NonlindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonlindelof_univ : ¬IsLindelof (univ : Set X)
