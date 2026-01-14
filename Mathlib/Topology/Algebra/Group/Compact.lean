/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Sets.Compacts

/-!
# Additional results on topological groups

A result on topological groups that has been separated out
as it requires more substantial imports developing positive compacts.
-/


universe u
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Every topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive
  /-- Every topological additive group
  in which there exists a compact set with nonempty interior is locally compact. -/]
theorem TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    (K : PositiveCompacts G) : LocallyCompactSpace G :=
  let ⟨_x, hx⟩ := K.interior_nonempty
  K.isCompact.locallyCompactSpace_of_mem_nhds_of_group (mem_interior_iff_mem_nhds.1 hx)
