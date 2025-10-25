/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Discreteness of subgroups in archimedean ordered groups

This file contains some supplements to the results in `Mathlib.Topology.Algebra.Order.Archimedean`,
involving discreteness of subgroups, which require heavier imports.
-/

/-- Any non-trivial linearly ordered archimedean additive group is either cyclic, or densely
ordered, exclusively. -/
lemma LinearOrderedAddCommGroup.isAddCyclic_iff_not_denselyOrdered {A : Type*}
    [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A] [Archimedean A] [Nontrivial A] :
    IsAddCyclic A ↔ ¬ DenselyOrdered A := by
  rw [← discrete_iff_not_denselyOrdered]
  constructor
  · rintro ⟨g, hg⟩
    constructor
    apply int_orderAddMonoidIso_of_isLeast_pos (x := |g|)
    constructor
    · rw [Set.mem_setOf, abs_pos]
      rintro rfl
      obtain ⟨h, hh⟩ := exists_ne (0 : A)
      obtain ⟨n, rfl⟩ := hg h
      simp at hh
    · refine mem_lowerBounds.mpr fun x hx ↦ ?_
      obtain ⟨n, rfl⟩ := hg x
      rw [← abs_eq_self.mpr hx.le, abs_zsmul]
      exact le_smul_of_one_le_left (abs_nonneg _) (Int.one_le_abs fun hn ↦ by simp_all)
  · rintro ⟨e⟩
    exact e.isAddCyclic.mpr inferInstance

/-- Any non-trivial linearly ordered mul-archimedean group is either cyclic, or densely ordered,
exclusively. -/
@[to_additive existing]
lemma LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G] [Nontrivial G] :
    IsCyclic G ↔ ¬ DenselyOrdered G := by
  rw [← discrete_iff_not_denselyOrdered]
  constructor
  · rintro ⟨g, hg⟩
    constructor
    apply multiplicative_int_orderMonoidIso_of_isLeast_one_lt (x := |g|ₘ)
    constructor
    · rw [Set.mem_setOf, one_lt_mabs]
      rintro rfl
      obtain ⟨h, hh⟩ := exists_ne (1 : G)
      obtain ⟨n, rfl⟩ := hg h
      simp at hh
    · refine mem_lowerBounds.mpr fun x hx ↦ ?_
      obtain ⟨n, rfl⟩ := hg x
      rw [← mabs_eq_self.mpr hx.le, mabs_zpow]
      conv_lhs => rw [← zpow_one |g|ₘ]
      exact zpow_le_zpow_right (one_le_mabs _) (Int.one_le_abs fun hn ↦ by simp_all)
  · rintro ⟨e⟩
    exact e.isCyclic.mpr inferInstance

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

@[to_additive]
instance [DiscreteTopology G] : IsCyclic G := by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h ↦
    haveI := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

/-- In an Archimedean densely linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean linearly ordered additive group (with the order topology), a
subgroup is discrete iff it is cyclic. -/]
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
