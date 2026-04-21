/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# When a proper action is properly discontinuous

This file proves that if a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

## Main statements

* `properlyDiscontinuousSMul_iff_properSMul`: If a discrete group acts on a T2 space `X` such that
  `X × X` is compactly generated, and if the action is continuous in the second variable,
  then the action is properly discontinuous if and only if it is proper.
* `MulAction.properSMul_iff_isCompact_setOf_inter_nonempty`: if `G` is a topological group acting
  continuously on a T2 space `X` such that `X × X` is compactly generated, then the action is
  proper iff, for each pair of compacts `U, V ⊆ X`, the set of `g : G` such that `g • U` intersects
  `V` is compact.

## Tags

group action, proper action, properly discontinuous, compactly generated
-/
set_option backward.defeqAttrib.useBackward true

open scoped Pointwise

open Prod Set

public section

variable {G X : Type*} [TopologicalSpace X] [Group G]
  [TopologicalSpace G] [MulAction G X] [CompactlyGeneratedSpace (X × X)] [T2Space X]

/-- The `G`-action on `X` is proper iff, for each pair of compacts `U, V` in `X`,
the set of `g` such that `U` intersects `g • V` is compact.

See `ProperSMul.isCompact_setOf_inter_nonempty`
for a one-way implication with fewer conditions.

**Note**: We assume `CompactlyCoherentSpace (X × X)`
as this is the minimal assumption needed to make the proof work;
but this follows from various more familiar conditions,
such as `FirstCountableTopology X`.
Importing `Mathlib.Topology.Sequences` makes this implication available.
-/
@[to_additive /--
The `G`-action on `X` is proper iff, for each pair of compacts `U, V` in `X`,
the set of `g` such that `U` intersects `g +ᵥ V` is compact.

See `ProperVAdd.isCompact_setOf_inter_nonempty`
for a one-way implication with fewer conditions.

**Note**: We assume `CompactlyCoherentSpace (X × X)`
as this is the minimal assumption needed to make the proof work;
but this follows from various more familiar conditions,
such as `FirstCountableTopology X`.
Importing `Mathlib.Topology.Sequences` makes this implication available.
-/]
lemma MulAction.properSMul_iff_isCompact_setOf_inter_nonempty [ContinuousSMul G X] :
    ProperSMul G X ↔
    (∀ {U V : Set X}, IsCompact U → IsCompact V → IsCompact {g : G | (g • U ∩ V).Nonempty}) := by
  refine ⟨fun h ↦ ProperSMul.isCompact_setOf_inter_nonempty, fun h ↦ ⟨?_⟩⟩
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun {K} hK ↦ ?_⟩
  -- First reduce to the case `K = U × V`.
  let U := Prod.fst '' K
  let V := Prod.snd '' K
  have hU : IsCompact U := hK.image continuous_fst
  have hV : IsCompact V := hK.image continuous_snd
  suffices IsCompact ((fun (gx : G × X) ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (U ×ˢ V)) by
    apply this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop)
    exact Set.preimage_mono Set.subset_fst_image_prod_snd_image
  apply ((h hV hU).prod hV).of_isClosed_subset
  · exact (hU.prod hV).isClosed.preimage (by fun_prop)
  · exact fun ⟨g, x⟩ ⟨hgx, hgx'⟩ ↦ ⟨⟨g • x, smul_mem_smul_set hgx', hgx⟩, hgx'⟩

/-- If a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact. -/
@[to_additive]
theorem properlyDiscontinuousSMul_iff_properSMul [DiscreteTopology G] [ContinuousConstSMul G X] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by
  have : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  simp only [MulAction.properSMul_iff_isCompact_setOf_inter_nonempty, isCompact_iff_finite]
  rw [properlyDiscontinuousSMul_iff]

end
