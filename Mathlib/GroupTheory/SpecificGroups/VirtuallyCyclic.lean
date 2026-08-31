/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Virtually cyclic groups

A group is *virtually cyclic* if it has a cyclic subgroup of finite index.
Virtually cyclic groups are fundamental in geometric group theory: they are
exactly the elementary subgroups of hyperbolic groups, the groups with at most
two ends, and the conclusion of the curvature-free Margulis lemma of
Besson–Courtois–Gallot–Sambusetti.

## Main definitions and results

* `Group.IsVirtuallyCyclic` : a group with a cyclic subgroup of finite index.
* `Group.IsVirtuallyCyclic.isVirtuallyNilpotent` : virtually cyclic groups are
  virtually nilpotent (companion to `Group.IsNilpotent.isVirtuallyNilpotent`).
* `Group.IsVirtuallyCyclic.of_surjective`,
  `Group.IsVirtuallyCyclic.of_injective` : preservation under surjective
  homomorphisms and group embeddings. Instances provide the cyclic and finite base cases and
  closure under subgroups and quotients.

## TODO

* A finitely generated group is virtually cyclic iff it has ≤ 2 ends
  (requires ends of groups, not yet in Mathlib).
-/

@[expose] public section

namespace Group

variable (G : Type*) [Group G] {G' : Type*} [Group G']

/-- An additive group is **virtually cyclic** if it has a cyclic additive
subgroup of finite index. -/
@[mk_iff]
class _root_.AddGroup.IsVirtuallyAddCyclic (G : Type*) [AddGroup G] : Prop where
  exists_isAddCyclic_and_finiteIndex : ∃ H : AddSubgroup G, IsAddCyclic H ∧ H.FiniteIndex

/-- A group is **virtually cyclic** if it has a cyclic subgroup of finite
index. -/
@[mk_iff, to_additive existing]
class IsVirtuallyCyclic : Prop where
  exists_isCyclic_and_finiteIndex : ∃ H : Subgroup G, IsCyclic H ∧ H.FiniteIndex

variable {G}

/-- A cyclic group is virtually cyclic. -/
@[to_additive]
-- see Note [lower instance priority]
instance (priority := 100) [IsCyclic G] : IsVirtuallyCyclic G :=
  ⟨⊤, inferInstance, inferInstance⟩

/-- A finite group is virtually cyclic — via the trivial subgroup, which is
cyclic and of finite index. -/
@[to_additive]
-- see Note [lower instance priority]
instance (priority := 100) [Finite G] : IsVirtuallyCyclic G :=
  ⟨⊥, inferInstance, ⟨Subgroup.index_ne_zero_of_finite⟩⟩

-- TODO: additivize once Mathlib has additive nilpotency.
/-- A virtually cyclic group is virtually nilpotent: a cyclic group is
commutative, hence nilpotent. This slots next to
`Group.IsNilpotent.isVirtuallyNilpotent`. -/
theorem IsVirtuallyCyclic.isVirtuallyNilpotent [IsVirtuallyCyclic G] :
    IsVirtuallyNilpotent G := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  exact ⟨H, @CommGroup.isNilpotent _ hc.commGroup, hfi⟩

/-- Every subgroup of a virtually cyclic group is virtually cyclic. The
witness is `H.subgroupOf K`, cyclic because it is isomorphic to `H ⊓ K ≤ H`,
of finite index in `K` by `Subgroup.instFiniteIndex_subgroupOf`. -/
@[to_additive]
instance [IsVirtuallyCyclic G] (K : Subgroup G) : IsVirtuallyCyclic K := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  refine ⟨H.subgroupOf K, ?_, inferInstance⟩
  have hEq : H.subgroupOf K = (H ⊓ K).subgroupOf K := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have : IsCyclic (H ⊓ K :) := Subgroup.isCyclic_of_le inf_le_left
  rw [hEq]
  exact (Subgroup.subgroupOfEquivOfLe inf_le_right).isCyclic.mpr this

/-- The image of a virtually cyclic group under a surjective homomorphism is
virtually cyclic. Cyclicity of the image subgroup comes from
`isCyclic_of_surjective` along `f.subgroupMap`; finiteness of its index from
`Subgroup.index_map_dvd`. -/
@[to_additive]
theorem IsVirtuallyCyclic.of_surjective (f : G →* G') (hf : Function.Surjective f)
    [IsVirtuallyCyclic G] : IsVirtuallyCyclic G' := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  refine ⟨H.map f, isCyclic_of_surjective _ (f.subgroupMap_surjective H), ⟨fun h0 ↦ ?_⟩⟩
  apply hfi.index_ne_zero
  have hd := H.index_map_dvd hf
  rwa [h0, zero_dvd_iff] at hd

/-- A group embedding into a virtually cyclic group is virtually cyclic: it is
isomorphic to its range, a subgroup of the codomain. -/
@[to_additive]
theorem IsVirtuallyCyclic.of_injective (f : G →* G') (hf : Function.Injective f)
    [IsVirtuallyCyclic G'] : IsVirtuallyCyclic G :=
  .of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MonoidHom.ofInjective hf).symm.surjective

/-- Quotients of virtually cyclic groups are virtually cyclic. -/
@[to_additive]
instance [IsVirtuallyCyclic G] (N : Subgroup G) [N.Normal] : IsVirtuallyCyclic (G ⧸ N) :=
  .of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end Group
