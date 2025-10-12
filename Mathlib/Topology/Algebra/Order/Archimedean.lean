/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.GroupTheory.Archimedean
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topology on archimedean groups and fields

In this file we prove the following theorems:

- `Rat.denseRange_cast`: the coercion from `ℚ` to a linear ordered archimedean field has dense
  range;

- `AddSubgroup.dense_of_not_isolated_zero`, `AddSubgroup.dense_of_no_min`: two sufficient conditions
  for a subgroup of an archimedean linear ordered additive commutative group to be dense;

- `AddSubgroup.dense_or_cyclic`: an additive subgroup of an archimedean linear ordered additive
  commutative group `G` with order topology either is dense in `G` or is a cyclic subgroup.
-/

open Set

/-- Rational numbers are dense in a linear ordered archimedean field. -/
theorem Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : ℚ → 𝕜) :=
  dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 <| exists_rat_btwn h

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

variable [MulArchimedean G]

/-- A subgroup of an archimedean linear ordered multiplicative commutative group with order
topology is dense provided that for all `ε > 1` there exists an element of the subgroup
that belongs to `(1, ε)`. -/
@[to_additive /-- An additive subgroup of an archimedean linear ordered additive commutative group
with order topology is dense provided that for all positive `ε` there exists a positive element of
the subgroup that is less than `ε`. -/]
theorem dense_of_not_isolated_one (S : Subgroup G) (hS : ∀ ε > 1, ∃ g ∈ S, g ∈ Ioo 1 ε) :
    Dense (S : Set G) := by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 1]
    exact one_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b / a) (one_lt_div'.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zpow_mem_Ioc hg0 1 a).exists with ⟨m, hm⟩
  rw [one_mul] at hm
  refine ⟨g ^ m, zpow_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_div_iff_mul_lt'] at hg

/-- Let `S` be a nontrivial subgroup in an archimedean linear ordered multiplicative commutative
group `G` with order topology. If the set of elements of `S` that are greater than one
does not have a minimal element, then `S` is dense `G`. -/
@[to_additive /-- Let `S` be a nontrivial additive subgroup in an archimedean linear ordered
additive commutative group `G` with order topology. If the set of positive elements of `S` does not
have a minimal element, then `S` is dense `G`. -/]
theorem dense_of_no_min (S : Subgroup G) (hbot : S ≠ ⊥)
    (H : ¬∃ a : G, IsLeast { g : G | g ∈ S ∧ 1 < g } a) : Dense (S : Set G) := by
  refine S.dense_of_not_isolated_one fun ε ε1 => ?_
  contrapose! H
  exact exists_isLeast_one_lt hbot ε1 (disjoint_left.2 H)

/-- A subgroup of an archimedean linear ordered multiplicative commutative group `G` with order
topology either is dense in `G` or is a cyclic subgroup. -/
@[to_additive dense_or_cyclic
/-- An additive subgroup of an archimedean linear ordered additive commutative group `G`
with order topology either is dense in `G` or is a cyclic subgroup. -/]
theorem dense_or_cyclic (S : Subgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = closure {a} := by
  refine (em _).imp (dense_of_not_isolated_one S) fun h => ?_
  push_neg at h
  rcases h with ⟨ε, ε1, hε⟩
  exact cyclic_of_isolated_one ε1 (disjoint_left.2 hε)

variable [DenselyOrdered G]

/-- In an Archimedean densely linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean densely linearly ordered additive group (with the order
topology), a subgroup is discrete iff it is cyclic. -/]
lemma discrete_iff_cyclic {H : Subgroup G} :
    IsCyclic H ↔ DiscreteTopology H := by
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

variable [Nontrivial G]

/-- In a nontrivial densely linear ordered archimedean topological multiplicative group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `Subgroup.dense_or_cyclic` above. -/
@[to_additive dense_xor'_cyclic
/-- In a nontrivial densely linear ordered archimedean topological additive group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `AddSubgroup.dense_or_cyclic` above.
-/]
theorem dense_xor'_cyclic (s : Subgroup G) :
    Xor' (Dense (s : Set G)) (∃ a, s = .zpowers a) := by
  if hd : Dense (s : Set G) then
    simp only [hd, xor_true]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false, id, zpowers_eq_closure]
    exact s.dense_or_cyclic.resolve_left hd

@[to_additive]
theorem dense_iff_ne_zpowers {s : Subgroup G} :
    Dense (s : Set G) ↔ ∀ a, s ≠ .zpowers a := by
  simp [xor_iff_iff_not.1 s.dense_xor'_cyclic]

end Subgroup
