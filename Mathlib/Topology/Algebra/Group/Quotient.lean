/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Topology on the quotient group

In this file we define topology on `G ⧸ N`, where `N` is a subgroup of `G`,
and prove basic properties of this topology.
-/

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

@[deprecated (since := "2024-10-22")]
alias quotientMap_mk := isQuotientMap_mk

@[to_additive]
theorem continuous_mk {N : Subgroup G} : Continuous (mk : G → G ⧸ N) :=
  continuous_quot_mk

section ContinuousMulConst
variable [ContinuousConstSMul Gᵐᵒᵖ G] {N : Subgroup G}

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

/-- A quotient of a locally compact group is locally compact. -/
@[to_additive]
instance instLocallyCompactSpace [LocallyCompactSpace G] (N : Subgroup G) :
    LocallyCompactSpace (G ⧸ N) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

end ContinuousMulConst

section ContinuousMul

variable [ContinuousConstSMul Gᵐᵒᵖ G] {N : Subgroup G}

-- @[to_additive]
-- instance instContinuousSMul : ContinuousSMul G (G ⧸ N) where
--   continuous_smul := by
--     rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
--     exact continuous_mk.comp continuous_mul

-- @[to_additive]
-- instance instContinuousConstSMul : ContinuousConstSMul G (G ⧸ N) := inferInstance

@[to_additive (attr := deprecated "No deprecation message was provided." (since := "2024-10-05"))]
theorem continuous_smul₁ (x : G ⧸ N) : Continuous fun g : G => g • x :=
  continuous_id.smul continuous_const

variable (N)

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
  "Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient."]
theorem nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x) :=
  (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]
instance instFirstCountableTopology [FirstCountableTopology G] :
    FirstCountableTopology (G ⧸ N) where
  nhds_generated_countable := mk_surjective.forall.2 fun x ↦ nhds_eq N x ▸ inferInstance

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
  "The quotient of a second countable additive topological group by a subgroup is second
  countable."]
instance instSecondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ N) :=
  ContinuousConstSMul.secondCountableTopology

@[to_additive (attr := deprecated "No deprecation message was provided." (since := "2024-08-05"))]
theorem nhds_one_isCountablyGenerated [FirstCountableTopology G] [N.Normal] :
    (𝓝 (1 : G ⧸ N)).IsCountablyGenerated :=
  inferInstance

end ContinuousMul

variable [IsTopologicalGroup G] (N : Subgroup G)

@[to_additive]
instance instIsTopologicalGroup [N.Normal] : IsTopologicalGroup (G ⧸ N) where
  continuous_mul := by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive (attr := deprecated "No deprecation message was provided." (since := "2024-08-05"))]
theorem _root_.topologicalGroup_quotient [N.Normal] : IsTopologicalGroup (G ⧸ N) :=
  instIsTopologicalGroup N

@[to_additive]
theorem isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsClosedMap ((↑) : G → G ⧸ H) := by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage, preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]
instance instT3Space [N.Normal] [hN : IsClosed (N : Set G)] : T3Space (G ⧸ N) := by
  rw [← QuotientGroup.ker_mk' N] at hN
  haveI := IsTopologicalGroup.t1Space (G ⧸ N) ((isQuotientMap_mk N).isClosed_preimage.mp hN)
  infer_instance

end QuotientGroup
