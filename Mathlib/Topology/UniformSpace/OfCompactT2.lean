/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Tactic.TautoSet

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

open Topology Filter UniformSpace Set
open scoped SetRel

variable {γ : Type*}

/-!
### Uniformity on compact spaces
-/


/-- The unique uniform structure inducing a given compact topological structure. -/
def uniformSpaceOfCompactR1 [TopologicalSpace γ] [CompactSpace γ] [R1Space γ] : UniformSpace γ where
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
    -- so x and y are inseparable
    have clV : ClusterPt (x, y) (𝓟 <| Vᶜ) := hxy.of_inf_right
    have ninsep_xy : ¬Inseparable x y := by
      intro h
      rw [← mem_closure_iff_clusterPt, (h.prod .rfl).mem_closed_iff isClosed_closure,
        closure_compl] at clV
      apply clV
      rw [mem_interior_iff_mem_nhds]
      exact nhds_le_nhdsSet (mem_diagonal y) V_in
    -- Since γ is compact and Hausdorff, it is T₄, hence T₃.
    -- So there are closed neighborhoods V₁ and V₂ of x and y contained in
    -- disjoint open neighborhoods U₁ and U₂.
    obtain
      ⟨U₁, -, V₁, V₁_in, U₂, -, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds_of_not_inseparable ninsep_xy
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
      · cases hzz'
        simp only [W, U₃, mem_union, mem_prod]
        tauto_set
    -- So W ○ W ∈ F by definition of F
    have : W ○ W ∈ F := mem_lift' W_in
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ :=
      clusterPt_iff_nonempty.mp hxy.of_inf_left hV₁₂ this
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    simp only [W, U₃, mem_union, mem_prod] at huw hwv
    tauto_set
  nhds_eq_comap_uniformity x := by
    simp_rw [nhdsSet_diagonal, comap_iSup, nhds_prod_eq, comap_prod, Function.comp_def, comap_id']
    rw [iSup_split _ (Inseparable x)]
    conv_rhs =>
      congr
      · enter [1, i, 1, hi]
        rw [← hi.nhds_eq, comap_const_of_mem fun V => mem_of_mem_nhds]
      · enter [1, i, 1, hi]
        rw [(not_specializes_iff_exists_open.1 (mt Specializes.inseparable hi)).elim
          fun S hS => comap_const_of_notMem (hS.1.mem_nhds hS.2.1) hS.2.2]
    rw [iSup_subtype', @iSup_const _ _ _ _ ⟨⟨x, .rfl⟩⟩]
    simp
