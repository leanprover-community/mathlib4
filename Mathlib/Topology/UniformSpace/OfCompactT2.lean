/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Defs

/-!
# Compact separated uniform spaces

## Main statement

* `uniformSpace_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described by `compactSpace_uniformity`.

## Implementation notes

The construction `uniformSpace_of_compact_t2` is not declared as an instance, as it would badly
loop.

## Tags

uniform space, uniform continuity, compact space
-/

open Topology Filter UniformSpace Set
open scoped SetRel

variable {γ : Type*}

/-!
### Uniformity on compact spaces
-/


/-- The unique uniform structure inducing a given compact topological structure. -/
def uniformSpaceOfCompactT2 [TopologicalSpace γ] [CompactSpace γ] [T2Space γ] : UniformSpace γ where
  uniformity := 𝓝ˢ (diagonal γ)
  symm := continuous_swap.tendsto_nhdsSet fun _ => Eq.symm
  comp := by
      /-
        This is the difficult part of the proof. We need to prove that, for each neighborhood `W`
        of the diagonal `Δ`, there exists a smaller neighborhood `V` such that `V ○ V ⊆ W`.
      -/
    set 𝓝Δ := 𝓝ˢ (diagonal γ)
    -- The filter of neighborhoods of Δ
    set F := 𝓝Δ.lift' fun s : Set (γ × γ) => s ○ s
    -- Compositions of neighborhoods of Δ
    -- If this weren't true, then there would be V ∈ 𝓝Δ such that F ⊓ 𝓟 Vᶜ ≠ ⊥
    rw [le_iff_forall_inf_principal_compl]
    intro V V_in
    by_contra H
    haveI : NeBot (F ⊓ 𝓟 Vᶜ) := ⟨H⟩
    -- Hence compactness would give us a cluster point (x, y) for F ⊓ 𝓟 Vᶜ
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ p : γ × γ, ClusterPt p (F ⊓ 𝓟 Vᶜ) := exists_clusterPt_of_compactSpace _
    -- In particular (x, y) is a cluster point of 𝓟 Vᶜ, hence is not in the interior of V,
    -- and a fortiori not in Δ, so x ≠ y
    have clV : ClusterPt (x, y) (𝓟 <| Vᶜ) := hxy.of_inf_right
    have : (x, y) ∉ interior V := by
      have : (x, y) ∈ closure Vᶜ := by rwa [mem_closure_iff_clusterPt]
      rwa [closure_compl] at this
    have diag_subset : diagonal γ ⊆ interior V := subset_interior_iff_mem_nhdsSet.2 V_in
    have x_ne_y : x ≠ y := mt (@diag_subset (x, y)) this
    -- Since γ is compact and Hausdorff, it is T₄, hence T₃.
    -- So there are closed neighborhoods V₁ and V₂ of x and y contained in
    -- disjoint open neighborhoods U₁ and U₂.
    obtain
      ⟨U₁, _, V₁, V₁_in, U₂, _, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds x_ne_y
    -- We set U₃ := (V₁ ∪ V₂)ᶜ so that W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃ is an open
    -- neighborhood of Δ.
    let U₃ := (V₁ ∪ V₂)ᶜ
    have U₃_op : IsOpen U₃ := (V₁_cl.union V₂_cl).isOpen_compl
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃
    have W_in : W ∈ 𝓝Δ := by
      rw [mem_nhdsSet_iff_forall]
      rintro ⟨z, z'⟩ (rfl : z = z')
      refine IsOpen.mem_nhds ?_ ?_
      · apply_rules [IsOpen.union, IsOpen.prod]
      · simp only [W, mem_union, mem_prod, and_self_iff]
        exact (_root_.em _).imp_left fun h => union_subset_union VU₁ VU₂ h
    -- So W ○ W ∈ F by definition of F
    have : W ○ W ∈ F := by simpa only using mem_lift' W_in
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    -- Indeed assume for contradiction there is some (u, v) in the intersection.
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ :=
      clusterPt_iff_nonempty.mp hxy.of_inf_left hV₁₂ this
    -- So u ∈ V₁, v ∈ V₂, and there exists some w such that (u, w) ∈ W and (w ,v) ∈ W.
    -- Because u is in V₁ which is disjoint from U₂ and U₃, (u, w) ∈ W forces (u, w) ∈ U₁ ×ˢ U₁.
    have uw_in : (u, w) ∈ U₁ ×ˢ U₁ :=
      (huw.resolve_right fun h => h.1 <| Or.inl u_in).resolve_right fun h =>
        hU₁₂.le_bot ⟨VU₁ u_in, h.1⟩
    -- Similarly, because v ∈ V₂, (w ,v) ∈ W forces (w, v) ∈ U₂ ×ˢ U₂.
    have wv_in : (w, v) ∈ U₂ ×ˢ U₂ :=
      (hwv.resolve_right fun h => h.2 <| Or.inr v_in).resolve_left fun h =>
        hU₁₂.le_bot ⟨h.2, VU₂ v_in⟩
    -- Hence w ∈ U₁ ∩ U₂ which is empty.
    -- So we have a contradiction
    exact hU₁₂.le_bot ⟨uw_in.2, wv_in.1⟩
  nhds_eq_comap_uniformity x := by
    simp_rw [nhdsSet_diagonal, comap_iSup, nhds_prod_eq, comap_prod, Function.comp_def, comap_id']
    rw [iSup_split_single _ x, comap_const_of_mem fun V => mem_of_mem_nhds]
    suffices ∀ y ≠ x, comap (fun _ : γ ↦ x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x by simpa
    intro y hxy
    simp [comap_const_of_notMem (compl_singleton_mem_nhds hxy) (not_not_intro rfl)]
