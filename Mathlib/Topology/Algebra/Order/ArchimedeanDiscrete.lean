/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Discreteness of subgroups in archimedean ordered groups

This file contains some supplements to the results in
`Mathlib/Topology/Algebra/Order/Archimedean.lean`, involving discreteness of subgroups, which
require heavier imports.
-/

public section

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
    simp only [Subtype.ext_iff, show n = 0 by lia, zpow_zero, coe_one]
  · simp_all

variable [MulArchimedean G]

@[to_additive]
instance [DiscreteTopology G] : IsCyclic G := by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h ↦
    have := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

/-- A subgroup of an archimedean linear ordered multiplicative commutative group `G` with order
topology either is dense in `G` or is a cyclic subgroup. -/
@[to_additive dense_or_isCyclic
/-- An additive subgroup of an archimedean linear ordered additive commutative group `G`
with order topology either is dense in `G` or is a cyclic subgroup. -/]
theorem dense_or_isCyclic (H : Subgroup G) : Dense (H : Set G) ∨ IsCyclic H := by
  refine (em _).imp (dense_of_not_isolated_one H) fun h => ?_
  push Not at h
  rcases h with ⟨ε, ε1, hε⟩
  exact isCyclic_of_disjoint_Ioo_one ε1 (Set.disjoint_left.2 hε)

@[to_additive (attr := deprecated (since := "2026-08-30")) dense_or_cyclic]
alias dense_or_cyclic := dense_or_isCyclic

/-- In a nontrivial densely linear ordered archimedean topological multiplicative group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `Subgroup.dense_or_cyclic` above. -/
@[to_additive
/-- In a nontrivial densely linear ordered archimedean topological additive group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `AddSubgroup.dense_or_cyclic` above.
-/]
theorem dense_xor_isCyclic [Nontrivial G] [DenselyOrdered G] (H : Subgroup G) :
    Xor (Dense (H : Set G)) (IsCyclic H) := by
  if hd : Dense (H : Set G) then
    simp only [hd, xor_true, H.isCyclic_iff_exists_zpowers_eq_top]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false]
    exact H.dense_or_isCyclic.resolve_left hd

@[to_additive (attr := deprecated (since := "2026-08-30")) dense_xor_cyclic]
alias dense_xor_cyclic := dense_xor_isCyclic

@[to_additive (attr := deprecated (since := "2026-04-27"))]
alias dense_xor'_cyclic := dense_xor_isCyclic

@[to_additive]
theorem dense_iff_not_isCyclic [Nontrivial G] [DenselyOrdered G] {H : Subgroup G} :
    Dense (H : Set G) ↔ ¬IsCyclic H := by
  simp [xor_iff_iff_not.1 H.dense_xor_isCyclic]

@[to_additive (attr := deprecated (since := "2026-08-30"))]
alias dense_iff_ne_zpowers := dense_iff_not_isCyclic

/-- In an Archimedean linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean linearly ordered additive group (with the order topology), a
subgroup is discrete iff it is cyclic. -/]
lemma isCyclic_iff_discreteTopology {H : Subgroup G} : IsCyclic H ↔ DiscreteTopology H := by
  refine ⟨fun h ↦ ?_, fun hA ↦ H.dense_or_isCyclic.elim (fun h ↦ ?_) id⟩
  · rcases H.isCyclic_iff_exists_zpowers_eq_top.mp h with ⟨g, rfl⟩
    infer_instance
  · -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain rfl : H = ⊤ := by
      rw [← coe_eq_univ, ← (dense_iff_closure_eq.mp h), H.isClosed_of_discrete.closure_eq]
    have : DiscreteTopology G := by rwa [← (Homeomorph.Set.univ G).discreteTopology_iff]
    infer_instance

@[to_additive (attr := deprecated (since := "2026-08-30"))]
alias discrete_iff_cyclic := isCyclic_iff_discreteTopology

end Subgroup
