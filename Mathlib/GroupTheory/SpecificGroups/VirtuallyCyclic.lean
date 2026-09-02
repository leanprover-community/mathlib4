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
  homomorphisms and group embeddings. Instances provide the cyclic and finite
  base cases and closure under subgroups and quotients.

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
  ⟨⊥, inferInstance, inferInstance⟩

/-- The preimage of a finite-index subgroup has finite index. -/
@[to_additive]
theorem _root_.Subgroup.FiniteIndex.comap {H : Subgroup G'} (hfi : H.FiniteIndex)
    (f : G →* G') : (H.comap f).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_comap]
    exact (Subgroup.instFiniteIndex_subgroupOf H f.range).index_ne_zero⟩

/-- The image of a finite-index subgroup under a surjective homomorphism has
finite index. -/
@[to_additive]
theorem _root_.Subgroup.FiniteIndex.map_of_surjective {H : Subgroup G}
    (hfi : H.FiniteIndex) {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).FiniteIndex := by
  refine ⟨fun h0 => hfi.index_ne_zero ?_⟩
  have hd := H.index_map_dvd hf
  rwa [h0, zero_dvd_iff] at hd

/-- The restriction of an injective homomorphism to a preimage subgroup is
injective. -/
@[to_additive]
theorem _root_.MonoidHom.subgroupComap_injective_of_injective (f : G →* G')
    (H : Subgroup G') (hf : Function.Injective f) :
    Function.Injective (f.subgroupComap H) := by
  intro a b h
  have h2 : f (a : G) = f (b : G) := congrArg Subtype.val h
  exact Subtype.ext (hf h2)

variable (G) in
/-- A virtually cyclic group has a subgroup that is cyclic, of finite index
and normal: the normal core of any cyclic finite-index subgroup. -/
@[to_additive]
theorem IsVirtuallyCyclic.exists_isCyclic_and_finiteIndex_and_normal [IsVirtuallyCyclic G] :
    ∃ H : Subgroup G, IsCyclic H ∧ H.FiniteIndex ∧ H.Normal := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  exact ⟨H.normalCore, Subgroup.isCyclic_of_le H.normalCore_le, inferInstance, inferInstance⟩

/-- A virtually cyclic group is virtually nilpotent: a cyclic group is
commutative, hence nilpotent. This slots next to
`Group.IsNilpotent.isVirtuallyNilpotent`. -/
@[to_additive]
theorem IsVirtuallyCyclic.isVirtuallyNilpotent [IsVirtuallyCyclic G] :
    IsVirtuallyNilpotent G := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  exact ⟨H, inferInstance, hfi⟩

/-- The image of a virtually cyclic group under a surjective homomorphism is
virtually cyclic. -/
@[to_additive]
theorem IsVirtuallyCyclic.of_surjective (f : G →* G') (hf : Function.Surjective f)
    [IsVirtuallyCyclic G] : IsVirtuallyCyclic G' := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G›.exists_isCyclic_and_finiteIndex
  exact ⟨H.map f, isCyclic_of_surjective _ (f.subgroupMap_surjective H),
    hfi.map_of_surjective hf⟩

/-- A group embedding into a virtually cyclic group is virtually cyclic: the
preimage of the cyclic finite-index subgroup witnesses it. -/
@[to_additive]
theorem IsVirtuallyCyclic.of_injective (f : G →* G') (hf : Function.Injective f)
    [IsVirtuallyCyclic G'] : IsVirtuallyCyclic G := by
  obtain ⟨H, hc, hfi⟩ := ‹IsVirtuallyCyclic G'›.exists_isCyclic_and_finiteIndex
  exact ⟨H.comap f,
    isCyclic_of_injective (f.subgroupComap H)
      (f.subgroupComap_injective_of_injective H hf),
    hfi.comap f⟩

/-- Every subgroup of a virtually cyclic group is virtually cyclic. -/
@[to_additive]
instance [IsVirtuallyCyclic G] (K : Subgroup G) : IsVirtuallyCyclic K :=
  .of_injective K.subtype K.subtype_injective

/-- Quotients of virtually cyclic groups are virtually cyclic. -/
@[to_additive]
instance [IsVirtuallyCyclic G] (N : Subgroup G) [N.Normal] : IsVirtuallyCyclic (G ⧸ N) :=
  .of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end Group
