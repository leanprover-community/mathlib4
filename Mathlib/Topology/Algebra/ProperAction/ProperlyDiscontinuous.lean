/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# When a proper action is properly discontinuous

This file proves that if a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

## Main statement
* `properlyDiscontinuousSMul_iff_properSMul`: If a discrete group acts on a T2 space `X` such that
  `X × X` is compactly generated, and if the action is continuous in the second variable,
  then the action is properly discontinuous if and only if it is proper.

## Tags

grouup action, proper action, properly discontinuous, compactly generated
-/

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]

open Prod Set

/-- If a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

There was an older version of this theorem which was changed to this one to make use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10) -/
theorem properlyDiscontinuousSMul_iff_properSMul [T2Space X] [DiscreteTopology G]
    [ContinuousConstSMul G X] [CompactlyGeneratedSpace (X × X)] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by
  constructor
  · intro h
    rw [properSMul_iff]
    -- We have to show that `f : (g, x) ↦ (g • x, x)` is proper.
    -- Continuity follows from continuity of `g • ·` and the fact that `G` has the
    -- discrete topology, thanks to `continuous_of_partial_of_discrete`.
    -- Because `X × X` is compactly generated, to show that f is proper
    -- it is enough to show that the preimage of a compact set `K` is compact.
    refine isProperMap_iff_isCompact_preimage.2
      ⟨(continuous_prod_of_discrete_left.2 continuous_const_smul).prodMk (by fun_prop),
      fun K hK ↦ ?_⟩
    -- We set `K' := pr₁(K) ∪ pr₂(K)`, which is compact because `K` is compact and `pr₁` and
    -- `pr₂` are continuous. We halso have that `K ⊆ K' × K'`, and `K` is closed because `X` is T2.
    -- Therefore `f ⁻¹ (K)` is also closed and `f ⁻¹ (K) ⊆ f ⁻¹ (K' × K')`, thus it suffices to
    -- show that `f ⁻¹ (K' × K')` is compact.
    let K' := fst '' K ∪ snd '' K
    have hK' : IsCompact K' := (hK.image continuous_fst).union (hK.image continuous_snd)
    let E := {g : G | Set.Nonempty ((g • ·) '' K' ∩ K')}
    -- The set `E` is finite because the action is properly discontinuous.
    have fin : Set.Finite E := by
      simp_rw [E, nonempty_iff_ne_empty]
      exact h.finite_disjoint_inter_image hK' hK'
    -- Therefore we can rewrite `f ⁻¹ (K' × K')` as a finite union of compact sets.
    have : (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K') =
        ⋃ g ∈ E, {g} ×ˢ ((g⁻¹ • ·) '' K' ∩ K') := by
      ext gx
      simp only [mem_preimage, mem_prod, nonempty_def, mem_inter_iff, mem_image,
        exists_exists_and_eq_and, mem_setOf_eq, singleton_prod, iUnion_exists, biUnion_and',
        mem_iUnion, exists_prop, E]
      constructor
      · exact fun ⟨gx_mem, x_mem⟩ ↦ ⟨gx.2, x_mem, gx.1, gx_mem,
          ⟨gx.2, ⟨⟨gx.1 • gx.2, gx_mem, by simp⟩, x_mem⟩, rfl⟩⟩
      · rintro ⟨x, -, g, -, ⟨-, ⟨⟨x', x'_mem, rfl⟩, ginvx'_mem⟩, rfl⟩⟩
        exact ⟨by simpa, by simpa⟩
    -- Indeed each set in this finite union is the product of a singleton and
    -- the intersection of the compact `K'` with its image by some element `g`, and this image is
    -- compact because `g • ·` is continuous.
    have : IsCompact ((fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K')) :=
      this ▸ fin.isCompact_biUnion fun g hg ↦
        isCompact_singleton.prod <| (hK'.image <| continuous_const_smul _).inter hK'
    -- We conclude as explained above.
    exact this.of_isClosed_subset (hK.isClosed.preimage <|
      (continuous_prod_of_discrete_left.2 continuous_const_smul).prodMk (by fun_prop)) <|
      preimage_mono fun x hx ↦ ⟨Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩⟩
  · intro h; constructor
    intro K L hK hL
    simp_rw [← nonempty_iff_ne_empty]
    -- We want to show that a subset of `G` is finite, but as `G` has the discrete topology it
    -- is enough to show that this subset is compact.
    apply IsCompact.finite_of_discrete
    -- Now set `h : (g, x) ↦ (g⁻¹ • x, x)`, because `f` is proper by hypothesis, so is `h`.
    have : IsProperMap (fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) :=
      (IsProperMap.prodMap (Homeomorph.isProperMap (Homeomorph.inv G)) isProperMap_id).comp <|
        ProperSMul.isProperMap_smul_pair
    --But we also have that `{g | Set.Nonempty ((g • ·) '' K ∩ L)} = h ⁻¹ (K × L)`, which
    -- concludes the proof.
    have eq : {g | Set.Nonempty ((g • ·) '' K ∩ L)} =
        fst '' ((fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) ⁻¹' (K ×ˢ L)) := by
      simp_rw [nonempty_def]
      ext g; constructor
      · exact fun ⟨_, ⟨x, x_mem, rfl⟩, hx⟩ ↦ ⟨(g, g • x), ⟨by simpa, hx⟩, rfl⟩
      · rintro ⟨gx, hgx, rfl⟩
        exact ⟨gx.2, ⟨gx.1⁻¹ • gx.2, hgx.1, by simp⟩, hgx.2⟩
    exact eq ▸ IsCompact.image (this.isCompact_preimage <| hK.prod hL) continuous_fst
