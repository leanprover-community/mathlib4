/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.Separation
import Mathlib.Topology.Support

#align_import topology.uniform_space.compact from "leanprover-community/mathlib"@"735b22f8f9ff9792cf4212d7cb051c4c994bc685"

/-!
# Compact separated uniform spaces

## Main statements

* `compactSpace_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

* `uniformSpace_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.

* **Heine-Cantor** theorem: continuous functions on compact uniform spaces with values in uniform
  spaces are automatically uniformly continuous. There are several variations, the main one is
  `CompactSpace.uniformContinuous_of_continuous`.

## Implementation notes

The construction `uniformSpace_of_compact_t2` is not declared as an instance, as it would badly
loop.

## Tags

uniform space, uniform continuity, compact space
-/


open scoped Classical
open Uniformity Topology Filter UniformSpace Set

variable {α β γ : Type*} [UniformSpace α] [UniformSpace β]

/-!
### Uniformity on compact spaces
-/


/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α := by
  refine nhdsSet_diagonal_le_uniformity.antisymm ?_
  have :
    (𝓤 (α × α)).HasBasis (fun U => U ∈ 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U := by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine (isCompact_diagonal.nhdsSet_basis_uniformity this).ge_iff.2 fun U hU => ?_
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_iUnion₂.2
    ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩
#align nhds_set_diagonal_eq_uniformity nhdsSet_diagonal_eq_uniformity

/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)
#align compact_space_uniformity compactSpace_uniformity

theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  refine UniformSpace.ext ?_
  have : @CompactSpace γ u.toTopologicalSpace := by rwa [h]
  have : @CompactSpace γ u'.toTopologicalSpace := by rwa [h']
  rw [@compactSpace_uniformity _ u, compactSpace_uniformity, h, h']
#align unique_uniformity_of_compact unique_uniformity_of_compact

/-- The unique uniform structure inducing a given compact topological structure. -/
def uniformSpaceOfCompactT2 [TopologicalSpace γ] [CompactSpace γ] [T2Space γ] : UniformSpace γ where
  uniformity := 𝓝ˢ (diagonal γ)
  symm := continuous_swap.tendsto_nhdsSet fun x => Eq.symm
  comp := by
    /-  This is the difficult part of the proof. We need to prove that, for each neighborhood `W`
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
    have : W ○ W ∈ F := @mem_lift' _ _ _ (fun s => s ○ s) _ W_in
      -- Porting note: was `by simpa only using mem_lift' W_in`
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    -- Indeed assume for contradiction there is some (u, v) in the intersection.
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ := clusterPt_iff.mp hxy.of_inf_left hV₁₂ this
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
    simp_rw [nhdsSet_diagonal, comap_iSup, nhds_prod_eq, comap_prod, (· ∘ ·), comap_id']
    rw [iSup_split_single _ x, comap_const_of_mem fun V => mem_of_mem_nhds]
    suffices ∀ y ≠ x, comap (fun _ : γ ↦ x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x by simpa
    intro y hxy
    simp [comap_const_of_not_mem (compl_singleton_mem_nhds hxy) (not_not_intro rfl)]
#align uniform_space_of_compact_t2 uniformSpaceOfCompactT2

/-!
### Heine-Cantor theorem
-/


/-- Heine-Cantor: a continuous function on a compact uniform space is uniformly
continuous. -/
theorem CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α → β}
    (h : Continuous f) : UniformContinuous f :=
calc map (Prod.map f f) (𝓤 α)
   = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
 _ ≤ 𝓝ˢ (diagonal β)                      := (h.prod_map h).tendsto_nhdsSet mapsTo_prod_map_diagonal
 _ ≤ 𝓤 β                                  := nhdsSet_diagonal_le_uniformity
#align compact_space.uniform_continuous_of_continuous CompactSpace.uniformContinuous_of_continuous

/-- Heine-Cantor: a continuous function on a compact set of a uniform space is uniformly
continuous. -/
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_restrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf
#align is_compact.uniform_continuous_on_of_continuous IsCompact.uniformContinuousOn_of_continuous

/-- If `s` is compact and `f` is continuous at all points of `s`, then `f` is
"uniformly continuous at the set `s`", i.e. `f x` is close to `f y` whenever `x ∈ s` and `y` is
close to `x` (even if `y` is not itself in `s`, so this is a stronger assertion than
`UniformContinuousOn s`). -/
theorem IsCompact.uniformContinuousAt_of_continuousAt {r : Set (β × β)} {s : Set α}
    (hs : IsCompact s) (f : α → β) (hf : ∀ a ∈ s, ContinuousAt f a) (hr : r ∈ 𝓤 β) :
    { x : α × α | x.1 ∈ s → (f x.1, f x.2) ∈ r } ∈ 𝓤 α := by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
  refine ⟨f a, htsymm.mk_mem_comm.1 (hb _ _ _ haU ?_), hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]
#align is_compact.uniform_continuous_at_of_continuous_at IsCompact.uniformContinuousAt_of_continuousAt

theorem Continuous.uniformContinuous_of_tendsto_cocompact {f : α → β} {x : β}
    (h_cont : Continuous f) (hx : Tendsto f (cocompact α) (𝓝 x)) : UniformContinuous f :=
  uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
          (hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt) <|
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ ∈ s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ ∈ s; · exact (h.2 h₂).2
    apply htr
    exact ⟨x, htsymm.mk_mem_comm.1 (hst h₁), hst h₂⟩
#align continuous.uniform_continuous_of_tendsto_cocompact Continuous.uniformContinuous_of_tendsto_cocompact

/-- If `f` has compact multiplicative support, then `f` tends to 1 at infinity. -/
@[to_additive "If `f` has compact support, then `f` tends to zero at infinity."]
theorem HasCompactMulSupport.is_one_at_infty {f : α → γ} [TopologicalSpace γ] [One γ]
    (h : HasCompactMulSupport f) : Tendsto f (cocompact α) (𝓝 1) := by
  -- Porting note: move to src/topology/support.lean once the port is over
  intro N hN
  rw [mem_map, mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage, image_eq_one_of_nmem_mulTSupport hv]
  exact mem_of_mem_nhds hN
#align has_compact_mul_support.is_one_at_infty HasCompactMulSupport.is_one_at_infty
#align has_compact_support.is_zero_at_infty HasCompactSupport.is_zero_at_infty

@[to_additive]
theorem HasCompactMulSupport.uniformContinuous_of_continuous {f : α → β} [One β]
    (h1 : HasCompactMulSupport f) (h2 : Continuous f) : UniformContinuous f :=
  h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty
#align has_compact_mul_support.uniform_continuous_of_continuous HasCompactMulSupport.uniformContinuous_of_continuous
#align has_compact_support.uniform_continuous_of_continuous HasCompactSupport.uniformContinuous_of_continuous

/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and `f` is continuous on `U × (univ : Set β)` for some neighborhood `U` of `x`. -/
theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    {f : α → β → γ} {x : α} {U : Set α} (hxU : U ∈ 𝓝 x) (h : ContinuousOn (↿f) (U ×ˢ univ)) :
    TendstoUniformly f (f x) (𝓝 x) := by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn (↿f) (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK
#align continuous_on.tendsto_uniformly ContinuousOn.tendstoUniformly

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x`
if `α` is weakly locally compact and `β` is compact. -/
theorem Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    (f : α → β → γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn (↿f) (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK
#align continuous.tendsto_uniformly Continuous.tendstoUniformly

/-- In a product space `α × β`, assume that a function `f` is continuous on `s × k` where `k` is
compact. Then, along the fiber above any `q ∈ s`, `f` is transversely uniformly continuous, i.e.,
if `p ∈ s` is close enough to `q`, then `f p x` is uniformly close to `f q x` for all `x ∈ k`. -/
lemma IsCompact.mem_uniformity_of_prod
    {α β E : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace E]
    {f : α → β → E} {s : Set α} {k : Set β} {q : α} {u : Set (E × E)}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) (hq : q ∈ s) (hu : u ∈ 𝓤 E) :
    ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ k, (f p x, f q x) ∈ u := by
  apply hk.induction_on (p := fun t ↦ ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ t, (f p x, f q x) ∈ u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx ↦ hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v ∩ v', inter_mem v_mem v'_mem, fun p hp x hx ↦ ?_⟩
    rcases hx with h'x|h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      ∃ v ∈ 𝓝[s] q, ∃ w ∈ 𝓝[k] x, v ×ˢ w ⊆ f.uncurry ⁻¹' {z | (f q x, z) ∈ u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy ↦ ?_⟩
    have A : (f q x, f p y) ∈ u' := hvw (⟨hp, hy⟩ : (p, y) ∈ v ×ˢ w)
    have B : (f q x, f q y) ∈ u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) ∈ v ×ˢ w)
    exact hu' (prod_mk_mem_compRel (u'_symm A) B)

section UniformConvergence

/-- An equicontinuous family of functions defined on a compact uniform space is automatically
uniformly equicontinuous. -/
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type*} {F : ι → β → α}
    [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F := by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h
#align compact_space.uniform_equicontinuous_of_equicontinuous CompactSpace.uniformEquicontinuous_of_equicontinuous

end UniformConvergence
