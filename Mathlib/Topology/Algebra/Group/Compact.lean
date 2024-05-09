/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts

#align_import topology.algebra.group.compact from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Additional results on topological groups

Two results on topological groups that have been separated out as they require more substantial
imports developing either positive compacts or the compact open topology.

-/


open scoped Classical
open Set Filter TopologicalSpace Function

open scoped Classical
open Topology Filter Pointwise

universe u v w x

variable {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section

variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

/-- Every topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive
  "Every topological additive group
  in which there exists a compact set with nonempty interior is locally compact."]
theorem TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    (K : PositiveCompacts G) : LocallyCompactSpace G :=
  let ⟨_x, hx⟩ := K.interior_nonempty
  K.isCompact.locallyCompactSpace_of_mem_nhds_of_group (mem_interior_iff_mem_nhds.1 hx)
#align topological_space.positive_compacts.locally_compact_space_of_group TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
#align topological_space.positive_compacts.locally_compact_space_of_add_group TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_addGroup

end

section Quotient

variable [Group G] [TopologicalSpace G] [TopologicalGroup G] {Γ : Subgroup G}

@[to_additive]
instance QuotientGroup.continuousSMul [LocallyCompactSpace G] : ContinuousSMul G (G ⧸ Γ) where
  continuous_smul := by
    let F : G × G ⧸ Γ → G ⧸ Γ := fun p => p.1 • p.2
    change Continuous F
    have H : Continuous (F ∘ fun p : G × G => (p.1, QuotientGroup.mk p.2)) := by
      change Continuous fun p : G × G => QuotientGroup.mk (p.1 * p.2)
      exact continuous_coinduced_rng.comp continuous_mul
    exact QuotientMap.continuous_lift_prod_right quotientMap_quotient_mk' H
#align quotient_group.has_continuous_smul QuotientGroup.continuousSMul
#align quotient_add_group.has_continuous_vadd QuotientAddGroup.continuousVAdd

end Quotient
