/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.GroupWithZero

/-!

# Topological monoids with open units

We say that a topological monoid `M` has open units (`IsOpenUnits`) if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)` (`IsOpenUnits.of_isAdic`).

A non-example is `𝔸ₖ`, because the topology on ideles is not the induced topology from adeles.

This condition is necessary and sufficient for `U(R)` to be an open subspace of `X(R)`
for all affine scheme `X` over `R` and all affine open subscheme `U ⊆ X`.
-/

public section

open Topology

/--
We say that a topological monoid `M` has open units if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`.
-/
@[mk_iff]
class IsOpenUnits (M : Type*) [Monoid M] [TopologicalSpace M] : Prop where
  isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Mˣ → M)

namespace Units

variable {M : Type*} [Monoid M] [TopologicalSpace M] [IsOpenUnits M]

lemma isOpenEmbedding_val : IsOpenEmbedding (Units.val : Mˣ → M) :=
  IsOpenUnits.isOpenEmbedding_unitsVal

lemma isOpenMap_val : IsOpenMap (Units.val : Mˣ → M) := isOpenEmbedding_val.isOpenMap

end Units

instance (priority := 900) (M : Type*) [Monoid M] [TopologicalSpace M] [DiscreteTopology M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal :=
    .of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective
      fun _ _ ↦ isOpen_discrete _

instance (priority := 900) {M : Type*} [Group M] [TopologicalSpace M] [ContinuousInv M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal := toUnits_homeomorph.symm.isOpenEmbedding

instance (priority := 900) {M : Type*} [GroupWithZero M]
    [TopologicalSpace M] [ContinuousInv₀ M] [T1Space M] : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    convert! (isClosed_singleton (X := M) (x := 0)).isOpen_compl
    ext
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact isUnit_iff_ne_zero
