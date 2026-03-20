/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Fiberwise criteria for proper actions

In this file we show that if `G` acts continuously and transitively on `X` and the orbit map
of some point in `X` is proper (and suitable auxiliary conditions hold), then the action is a
proper action.
-/
open scoped Pointwise

public section

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]

/-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `U` intersects `g • V` is compact.

See `MulAction.properSMul_iff_isCompact_setOf_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/
@[to_additive /-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `U` intersects `g +ᵥ V` is compact.

See `AddAction.properVAdd_iff_isCompact_setOf_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/]
lemma ProperSMul.isCompact_setOf_inter_nonempty [ProperSMul G X]
    {U V : Set X} (hU : IsCompact U) (hV : IsCompact V) :
    IsCompact {g : G | (U ∩ g • V).Nonempty} := by
  convert ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage
    (hU.prod hV)).image continuous_fst
  ext x
  suffices (∃ u ∈ U, u ∈ x • V) ↔ ∃ v, x • v ∈ U ∧ v ∈ V by simpa
  rw [← (MulAction.toPerm x).exists_congr_right]
  simp

namespace MulAction

variable [ContinuousSMul G X]

/-- If `G` acts transitively on `X`, and the orbit map of a point in `X` is a proper map, then the
action is proper. -/
@[to_additive]
lemma properSMul_of_proper_orbitMap [IsTopologicalGroup G] [MulAction.IsPretransitive G X]
    {x : X} (hx : IsProperMap fun g : G ↦ g • x) : ProperSMul G X := by
  constructor
  let f : G × G → G × X := Prod.map id (fun g ↦ g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using (hx.prodMap hx).comp (ProperSMul.isProperMap_smul_pair (G := G))

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
lemma properSMul_iff_isCompact_setOf_inter_nonempty [T2Space X] [CompactlyCoherentSpace (X × X)] :
    ProperSMul G X ↔
    (∀ {U V : Set X}, IsCompact U → IsCompact V → IsCompact {g : G | (U ∩ g • V).Nonempty}) := by
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
  apply ((h hU hV).prod hV).of_isClosed_subset
  · exact (hU.isClosed.preimage <| by fun_prop).inter (hV.isClosed.preimage continuous_snd)
  · exact fun ⟨g, x⟩ ⟨hgx, hgx'⟩ ↦ ⟨⟨g • x, hgx, Set.smul_mem_smul_set hgx'⟩, hgx'⟩

end MulAction

end
