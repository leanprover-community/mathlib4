/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Discreteness of subgroups in archimedean ordered groups

This file contains some supplements to the results in `Mathlib.Topology.Algebra.Order.Archimedean`,
involving discreteness of subgroups, which require heavier imports.
-/

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]

/-- In a linearly ordered group with the order topology, the powers of a single element form a
discrete subgroup. -/
@[to_additive /-- In a linearly ordered additive group with the order topology, the multiples of a
single element form a discrete subgroup. -/]
instance instDiscreteTopologyZMultiples (g : G) : DiscreteTopology (zpowers g) := by
  wlog ha : 1 ≤ g
  · specialize this g⁻¹ (one_le_inv'.mpr (le_of_not_ge ha))
    rwa [zpowers_inv] at this
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [zpowers_one_eq_bot]
    exact Subsingleton.discreteTopology
  rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff]
  refine ⟨Set.Ioo (g ^ (-1 : ℤ)) (g ^ (1 : ℤ)), isOpen_Ioo, ?_⟩
  ext ⟨_, ⟨n, rfl⟩⟩
  constructor
  · simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro hn hn'
    rw [zpow_lt_zpow_iff_right ha] at hn hn'
    simp only [Subtype.ext_iff, show n = 0 by omega, zpow_zero, coe_one]
  · simp_all

variable [MulArchimedean G] [DenselyOrdered G]

/-- In an Archimedean densely linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean densely linearly ordered additive group (with the order
topology), a subgroup is discrete iff it is cyclic. -/]
lemma discrete_iff_cyclic {H : Subgroup G} :
    IsCyclic H ↔ DiscreteTopology H := by
  -- TODO: Is the `DenselyOrdered` hypothesis actually necessary here?
  rcases subsingleton_or_nontrivial G
  · simp [isCyclic_of_subsingleton, Subsingleton.discreteTopology]
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine fun hA ↦ this.resolve_left fun h ↦ ?_
    -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain ⟨U, hU⟩ := discreteTopology_subtype_iff'.mp hA 1 (by simp)
    obtain ⟨j, hj⟩ := mem_closure_iff.mp (h.diff_singleton 1 1) U hU.1
      (by simpa only [← Set.singleton_subset_iff, ← hU.2] using Set.inter_subset_left)
    grind

end Subgroup
