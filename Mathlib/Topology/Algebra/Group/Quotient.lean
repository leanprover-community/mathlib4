/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Continuous
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Topology on the quotient group

In this file we define topology on `G ⧸ N`, where `N` is a subgroup of `G`,
and prove basic properties of this topology.
-/

@[expose] public section

assert_not_exists Cardinal

open Topology
open scoped Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G]

namespace QuotientGroup

@[to_additive]
instance instTopologicalSpace (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuotient

@[to_additive]
instance [CompactSpace G] (N : Subgroup G) : CompactSpace (G ⧸ N) :=
  Quotient.compactSpace

@[to_additive]
theorem isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G → G ⧸ N) :=
  isQuotientMap_quot_mk

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_mk {N : Subgroup G} : Continuous (mk : G → G ⧸ N) :=
  continuous_quot_mk

section ContinuousMul

variable [SeparatelyContinuousMul G] {N : Subgroup G}

@[to_additive]
theorem isOpenMap_coe : IsOpenMap ((↑) : G → G ⧸ N) := isOpenMap_quotient_mk'_mul

@[to_additive]
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : G → G ⧸ N) :=
  MulAction.isOpenQuotientMap_quotientMk

@[to_additive (attr := simp)]
theorem dense_preimage_mk {s : Set (G ⧸ N)} : Dense ((↑) ⁻¹' s : Set G) ↔ Dense s :=
  isOpenQuotientMap_mk.dense_preimage_iff

@[to_additive]
theorem dense_image_mk {s : Set G} :
    Dense (mk '' s : Set (G ⧸ N)) ↔ Dense (s * (N : Set G)) := by
  rw [← dense_preimage_mk, preimage_image_mk_eq_mul]

@[to_additive]
instance instContinuousSMul {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {N : Subgroup G} : ContinuousSMul G (G ⧸ N) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

@[to_additive]
instance instContinuousConstSMul : ContinuousConstSMul G (G ⧸ N) where
  continuous_const_smul γ := by
    rw [← isOpenQuotientMap_mk.continuous_comp_iff]
    exact continuous_mk.comp <| continuous_const_smul γ

@[to_additive]
theorem t1Space_iff :
    T1Space (G ⧸ N) ↔ IsClosed (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one, MulAction.IsPretransitive.t1Space_iff G (mk 1),
      isClosed_coinduced]
  rfl

@[to_additive]
theorem discreteTopology_iff :
    DiscreteTopology (G ⧸ N) ↔ IsOpen (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one, MulAction.IsPretransitive.discreteTopology_iff G (mk 1),
      isOpen_coinduced]
  rfl

/-- The quotient of a topological group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological group) that the quotient is T3
(see `QuotientGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/
@[to_additive
/-- The quotient of a topological additive group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological additive group) that the
quotient is T3 (see `QuotientAddGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/]
instance instT1Space [hN : IsClosed (N : Set G)] :
    T1Space (G ⧸ N) :=
  t1Space_iff.mpr hN

-- TODO: `IsOpen` should be a class and this should be an instance
@[to_additive]
theorem discreteTopology (hN : IsOpen (N : Set G)) :
    DiscreteTopology (G ⧸ N) :=
  discreteTopology_iff.mpr hN

/-- A quotient of a locally compact group is locally compact. -/
@[to_additive]
instance instLocallyCompactSpace [LocallyCompactSpace G] (N : Subgroup G) :
    LocallyCompactSpace (G ⧸ N) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

variable (N)

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
  /-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/]
theorem nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x) :=
  (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]
instance instFirstCountableTopology [FirstCountableTopology G] :
    FirstCountableTopology (G ⧸ N) where
  nhds_generated_countable := mk_surjective.forall.2 fun x ↦ nhds_eq N x ▸ inferInstance

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
  /-- The quotient of a second countable additive topological group by a subgroup is second
  countable. -/]
instance instSecondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ N) :=
  ContinuousConstSMul.secondCountableTopology

end ContinuousMul

variable [IsTopologicalGroup G] (N : Subgroup G)

@[to_additive]
instance instIsTopologicalGroup [N.Normal] : IsTopologicalGroup (G ⧸ N) where
  continuous_mul := by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive]
theorem isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsClosedMap ((↑) : G → G ⧸ H) := by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage, preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]
instance instT3Space [N.Normal] [hN : IsClosed (N : Set G)] : T3Space (G ⧸ N) := by
  infer_instance

end QuotientGroup
