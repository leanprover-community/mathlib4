/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
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

-- this does not really belong thematically to this file, but it is not easy to find a place for it
-- without big import increases
@[to_additive (attr := simp)]
lemma zpowers_mabs (g : G) : zpowers |g|ₘ = zpowers g := by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

variable [TopologicalSpace G] [OrderTopology G]

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

variable [MulArchimedean G]

instance [DiscreteTopology G] : IsCyclic G := by
  nontriviality G
  have : ¬DenselyOrdered G := fun contra ↦
    haveI := contra.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G
  obtain ⟨e⟩ := (LinearOrderedCommGroup.discrete_iff_not_denselyOrdered G).mpr this
  exact e.isCyclic.mpr inferInstance

/-- In an Archimedean densely linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
lemma discrete_iff_cyclic {H : Subgroup G} : IsCyclic H ↔ DiscreteTopology H := by
  nontriviality G using isCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine fun hA ↦ this.elim (fun h ↦ ?_) id
    -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain rfl : H = ⊤ := by
      rw [← coe_eq_univ, ← (dense_iff_closure_eq.mp h), H.isClosed_of_discrete.closure_eq]
    have : DiscreteTopology G := by rwa [← (Homeomorph.Set.univ G).discreteTopology_iff]
    exact isCyclic_iff_exists_zpowers_eq_top.mp inferInstance

end Subgroup

namespace AddSubgroup
-- TODO: Currently it does not work to obtain these two declarations via `to_additive`, since
-- the formulation of `LinearOrderedCommGroup.discrete_iff_not_denselyOrdered` seems to defeat
-- the additivizer.

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [TopologicalSpace G]
  [OrderTopology G] [Archimedean G]

instance [DiscreteTopology G] : IsAddCyclic G := by
  nontriviality G
  have : ¬DenselyOrdered G := fun contra ↦
    haveI := contra.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G
  obtain ⟨e⟩ := (LinearOrderedAddCommGroup.discrete_iff_not_denselyOrdered G).mpr this
  exact e.isAddCyclic.mpr inferInstance

/-- In an Archimedean densely linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
lemma discrete_iff_cyclic {H : AddSubgroup G} : IsAddCyclic H ↔ DiscreteTopology H := by
  nontriviality G using isAddCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← AddSubgroup.zmultiples_eq_closure, Eq.comm (a := H)] at this
    refine fun hA ↦ this.elim (fun h ↦ ?_) id
    -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain rfl : H = ⊤ := by
      rw [← coe_eq_univ, ← (dense_iff_closure_eq.mp h), H.isClosed_of_discrete.closure_eq]
    have : DiscreteTopology G := by rwa [← (Homeomorph.Set.univ G).discreteTopology_iff]
    exact isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance

end AddSubgroup
