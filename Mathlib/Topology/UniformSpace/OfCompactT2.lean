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

* `uniformSpaceOfCompactR1`: every compact R1 topological structure is induced by a uniform
  structure. This uniform structure is described by `compactSpace_uniformity`.

## Implementation notes

The construction `uniformSpaceOfCompactR1` is not declared as an instance, as it would badly
loop.

## Tags

uniform space, uniform continuity, compact space
-/

open Uniformity Topology Filter UniformSpace Set

variable {γ : Type*}

/-!
### Uniformity on compact spaces
-/


/-- The unique uniform structure inducing a given compact topological structure. -/
def uniformSpaceOfCompactR1 [TopologicalSpace γ] [CompactSpace γ] [R1Space γ] : UniformSpace γ where
  uniformity := 𝓝ˢ {p | Inseparable p.fst p.snd}
  symm := continuous_swap.tendsto_nhdsSet fun _ => Inseparable.symm
  comp := by
    /-  This is the difficult part of the proof. We need to prove that, for each neighborhood `W`
        of the diagonal `Δ`, there exists a smaller neighborhood `V` such that `V ○ V ⊆ W`.
        -/
    set Δ : Set (γ × γ) := {p | Inseparable p.fst p.snd}
    set 𝓝Δ : Filter (γ × γ) := 𝓝ˢ Δ
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
      rwa [← mem_closure_iff_clusterPt, closure_compl] at clV
    have diag_subset : Δ ⊆ interior V := subset_interior_iff_mem_nhdsSet.2 V_in
    have x_ne_y : ¬Inseparable x y := mt (@diag_subset (x, y)) this
    -- Since γ is compact and Hausdorff, it is T₄, hence T₃.
    -- So there are closed neighborhoods V₁ and V₂ of x and y contained in
    -- disjoint open neighborhoods U₁ and U₂.
    obtain
      ⟨U₁, _, V₁, V₁_in, U₂, _, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds_of_separable x_ne_y
    -- We set U₃ := (V₁ ∪ V₂)ᶜ so that W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃ is an open
    -- neighborhood of Δ.
    let U₃ := (V₁ ∪ V₂)ᶜ
    have U₃_op : IsOpen U₃ := (V₁_cl.union V₂_cl).isOpen_compl
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃
    have W_in : W ∈ 𝓝Δ := by
      rw [mem_nhdsSet_iff_forall]
      rintro ⟨z, z'⟩ hzz'
      refine IsOpen.mem_nhds ?_ ?_
      · apply_rules [IsOpen.union, IsOpen.prod]
      · simp only [W, mem_union, mem_prod, and_self_iff,
          hzz'.mem_open_iff, U₁_op, U₂_op, U₃_op]
        exact (em _).imp_left fun h => union_subset_union VU₁ VU₂ h
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
    have nhds_diag : 𝓝ˢ {p : γ × γ | Inseparable p.fst p.snd} = ⨆ x, 𝓝 (x, x) := by
      apply le_antisymm
      · rw [nhdsSet_le]
        intro ⟨a, b⟩ h
        rw [(h.prod .rfl).nhds_eq]
        exact le_iSup (fun x => 𝓝 (x, x)) b
      · rw [iSup_le_iff]
        exact fun _ => nhds_le_nhdsSet Inseparable.rfl
    simp_rw [nhds_diag, comap_iSup, nhds_prod_eq, comap_prod, Function.comp_def, comap_id']
    rw [iSup_split _ (Inseparable x)]
    conv_rhs =>
      enter [1, 1, i, 1, hi]
      rw [← hi.nhds_eq, comap_const_of_mem fun V => mem_of_mem_nhds]
    rw [iSup_subtype', @iSup_const _ _ _ _ ⟨x, .rfl⟩]
    suffices ∀ y, ¬Inseparable x y → comap (fun _ : γ ↦ x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x by simpa
    intro y hxy
    have nxy : (closure {x})ᶜ ∈ 𝓝 y := by
      rw [← interior_compl, interior_mem_nhds, ← disjoint_principal_left, principal_singleton]
      rw [← disjoint_nhds_nhds_iff_not_inseparable] at hxy
      exact hxy.mono_left (pure_le_nhds x)
    simp [comap_const_of_notMem nxy (not_not_intro (subset_closure (mem_singleton x)))]
