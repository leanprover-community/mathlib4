/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Order.Filter.Tendsto
import Mathlib.Data.Set.Accumulate
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Defs.Ultrafilter

/-!
# Compact sets and compact spaces

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.

* `isCompact_generateFrom`: **Alexander's subbasis theorem** - suppose `X` is a topological space
  with a subbasis `S` and `s` is a subset of `X`, then `s` is compact if for any open cover of `s`
  with all elements taken from `S`, there is a finite subcover.
-/

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

-- compact sets
section Compact

lemma IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := hs hf

lemma IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
    {u : ι → X} (hf : Filter.map u f ≤ 𝓟 s) :
    ∃ x ∈ s, MapClusterPt x f u := hs hf

lemma IsCompact.exists_clusterPt_of_frequently {l : Filter X} (hs : IsCompact s)
    (hl : ∃ᶠ x in l, x ∈ s) : ∃ a ∈ s, ClusterPt a l :=
  let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩

lemma IsCompact.exists_mapClusterPt_of_frequently {l : Filter ι} {f : ι → X} (hs : IsCompact s)
    (hf : ∃ᶠ x in l, f x ∈ s) : ∃ a ∈ s, MapClusterPt a l f :=
  hs.exists_clusterPt_of_frequently hf

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) :
    sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

/-- The complement to a compact set belongs to a filter `f` if each `x ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X}
    (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsCompact.induction_on (hs : IsCompact s) {p : Set X → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := comk p he (fun _t ht _s hsub ↦ hmono hsub ht) (fun _s hs _t ht ↦ hunion hs ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a compact set and a closed set is a compact set. -/
theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) := by
  intro f hnf hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 inter_subset_left))
  have : x ∈ t := ht.mem_of_nhdsWithin_neBot <|
    hx.mono <| le_trans hstf (le_principal_iff.2 inter_subset_right)
  exact ⟨x, ⟨hsx, this⟩, hx⟩

/-- The intersection of a closed set and a compact set is a compact set. -/
theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a compact set is a compact set. -/
theorem IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

theorem IsCompact.image_of_continuousOn {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  haveI := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn

theorem IsCompact.adherence_nhdset {f : Filter X} (hs : IsCompact s) (hf₂ : f ≤ 𝓟 s)
    (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ ≠ ⊥) =>
    let ⟨x, hx, (hfx : ClusterPt x <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ ∀ f : Ultrafilter X, ↑f ≤ 𝓟 s → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  refine (forall_neBot_le_iff ?_).trans ?_
  · rintro f g hle ⟨x, hxs, hxf⟩
    exact ⟨x, hxs, hxf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds

theorem isCompact_iff_ultrafilter_le_nhds' :
    IsCompact s ↔ ∀ f : Ultrafilter X, s ∈ f → ∃ x ∈ s, ↑f ≤ 𝓝 x := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

/-- If a compact set belongs to a filter and this filter has a unique cluster point `y` in this set,
then the filter is less than or equal to `𝓝 y`. -/
lemma IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter X} {y : X}
    (hmem : s ∈ l) (h : ∀ x ∈ s, ClusterPt x l → x = y) : l ≤ 𝓝 y := by
  refine le_iff_ultrafilter.2 fun f hf ↦ ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  convert ← hx
  exact h x hxs (.mono (.of_le_nhds hx) hf)

/-- If values of `f : Y → X` belong to a compact set `s` eventually along a filter `l`
and `y` is a unique `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝 y` along `l`. -/
lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt {Y} {l : Filter Y} {y : X} {f : Y → X}
    (hs : IsCompact s) (hmem : ∀ᶠ x in l, f x ∈ s) (h : ∀ x ∈ s, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  hs.le_nhds_of_unique_clusterPt (mem_map.2 hmem) h

/-- For every open directed cover of a compact set, there exists a single element of the
cover which itself includes the set. -/
theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) :
    ∃ i, s ⊆ U i :=
  hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

lemma IsCompact.elim_nhds_subcover_nhdsSet' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x hx, U x hx ∈ 𝓝 x) : ∃ t : Finset s, (⋃ x ∈ t, U x.1 x.2) ∈ 𝓝ˢ s := by
  rcases hs.elim_finite_subcover (fun x : s ↦ interior (U x x.2)) (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩ with ⟨t, hst⟩
  refine ⟨t, mem_nhdsSet_iff_forall.2 fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (hst hx) with ⟨y, hyt, hy⟩
  refine mem_of_superset ?_ (subset_biUnion_of_mem hyt)
  exact mem_interior_iff_mem_nhds.1 hy

lemma IsCompact.elim_nhds_subcover_nhdsSet (hs : IsCompact s) {U : X → Set X}
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) : ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ (⋃ x ∈ t, U x) ∈ 𝓝ˢ s := by
  let ⟨t, ht⟩ := hs.elim_nhds_subcover_nhdsSet' (fun x _ => U x) hU
  classical
  exact ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩

theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
  (hs.elim_nhds_subcover_nhdsSet' U hU).imp fun _ ↦ subset_of_mem_nhdsSet

theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : X → Set X) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
  (hs.elim_nhds_subcover_nhdsSet hU).imp fun _ h ↦ h.imp_right subset_of_mem_nhdsSet

theorem IsCompact.elim_nhdsWithin_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set X)
    (hU : ∀ x (hx : x ∈ s), U x hx ∈ 𝓝[s] x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U x x.2 := by
  choose V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover' V V_nhds).imp fun t ht =>
    subset_trans ?_ (iUnion₂_mono fun x _ => hV x x.2)
  simpa [← iUnion_inter, ← iUnion_coe_set]

theorem IsCompact.elim_nhdsWithin_subcover (hs : IsCompact s) (U : X → Set X)
    (hU : ∀ x ∈ s, U x ∈ 𝓝[s] x) : ∃ t : Finset X, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
  choose! V V_nhds hV using fun x hx => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hU x hx)
  refine (hs.elim_nhds_subcover V V_nhds).imp fun t ⟨t_sub_s, ht⟩ =>
    ⟨t_sub_s, subset_trans ?_ (iUnion₂_mono fun x hx => hV x (t_sub_s x hx))⟩
  simpa [← iUnion_inter]

/-- The neighborhood filter of a compact set is disjoint with a filter `l` if and only if the
neighborhood filter of each point of this set is disjoint with `l`. -/
theorem IsCompact.disjoint_nhdsSet_left {l : Filter X} (hs : IsCompact s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine ⟨fun h x hx => h.mono_left <| nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂, biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)

/-- A filter `l` is disjoint with the neighborhood filter of a compact set if and only if it is
disjoint with the neighborhood filter of each point of this set. -/
theorem IsCompact.disjoint_nhdsSet_right {l : Filter X} (hs : IsCompact s) :
    Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

-- TODO: reformulate using `Disjoint`
/-- For every directed family of closed sets whose intersection avoids a compact set,
there exists a single element of the family which itself avoids this compact set. -/
theorem IsCompact.elim_directed_family_closed {ι : Type v} [Nonempty ι] (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅)
    (hdt : Directed (· ⊇ ·) t) : ∃ i : ι, s ∩ t i = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ t) (fun i => (htc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using hst)
      (hdt.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_notMem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, mem_iInter, mem_compl_iff] using ht⟩

-- TODO: reformulate using `Disjoint`
/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
theorem IsCompact.elim_finite_subfamily_closed {ι : Type v} (hs : IsCompact s)
    (t : ι → Set X) (htc : ∀ i, IsClosed (t i)) (hst : (s ∩ ⋂ i, t i) = ∅) :
    ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  hs.elim_directed_family_closed _ (fun _ ↦ isClosed_biInter fun _ _ ↦ htc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h ↦ biInter_subset_biInter_left h)

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
theorem IsCompact.inter_iInter_nonempty {ι : Type v} (hs : IsCompact s) (t : ι → Set X)
    (htc : ∀ i, IsClosed (t i)) (hst : ∀ u : Finset ι, (s ∩ ⋂ i ∈ u, t i).Nonempty) :
    (s ∩ ⋂ i, t i).Nonempty := by
  contrapose! hst
  exact hs.elim_finite_subfamily_closed t htc hst

/-- Cantor's intersection theorem for `iInter`:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    {ι : Type v} [hι : Nonempty ι] (t : ι → Set X) (htd : Directed (· ⊇ ·) t)
    (htn : ∀ i, (t i).Nonempty) (htc : ∀ i, IsCompact (t i)) (htcl : ∀ i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty := by
  let i₀ := hι.some
  suffices (t i₀ ∩ ⋂ i, t i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at htn ⊢
  apply mt ((htc i₀).elim_directed_family_closed t htcl)
  push_neg
  simp only [← nonempty_iff_ne_empty] at htn ⊢
  refine ⟨htd, fun i => ?_⟩
  rcases htd i₀ i with ⟨j, hji₀, hji⟩
  exact (htn j).mono (subset_inter hji₀ hji)

/-- Cantor's intersection theorem for `sInter`:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : ∀ U ∈ S, U.Nonempty)
    (hSc : ∀ U ∈ S, IsCompact U) (hScl : ∀ U ∈ S, IsClosed U) : (⋂₀ S).Nonempty := by
  rw [sInter_eq_iInter]
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (DirectedOn.directed_val hSd) (fun i ↦ hSn i i.2) (fun i ↦ hSc i i.2) (fun i ↦ hScl i i.2)

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : ℕ → Set X)
    (htd : ∀ i, t (i + 1) ⊆ t i) (htn : ∀ i, (t i).Nonempty) (ht0 : IsCompact (t 0))
    (htcl : ∀ i, IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
  have : ∀ i, t i ⊆ t 0 := fun i => tmono <| Nat.zero_le i
  have htc : ∀ i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι → Set X} (hs : IsCompact s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b → Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_of_finite_subcover
    (h : ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
      ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i) :
    IsCompact s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_notMem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm, compl_iInter₂]
  simpa only [compl_compl]

-- TODO: reformulate using `Disjoint`
/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem isCompact_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ →
      ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅) :
    IsCompact s :=
  isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem isCompact_iff_finite_subfamily_closed :
    IsCompact s ↔ ∀ {ι : Type u} (t : ι → Set X),
      (∀ i, IsClosed (t i)) → (s ∩ ⋂ i, t i) = ∅ → ∃ u : Finset ι, (s ∩ ⋂ i ∈ u, t i) = ∅ :=
  ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩

/-- If `s : Set (X × Y)` belongs to `𝓝 x ×ˢ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ×ˢ l`,
i.e., there exist an open `U ⊇ K` and `t ∈ l` such that `U ×ˢ t ⊆ s`. -/
theorem IsCompact.mem_nhdsSet_prod_of_forall {K : Set X} {Y} {l : Filter Y} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ×ˢ l) : s ∈ (𝓝ˢ K) ×ˢ l := by
  refine hK.induction_on (by simp) (fun t t' ht hs ↦ ?_) (fun t t' ht ht' ↦ ?_) fun x hx ↦ ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

theorem IsCompact.nhdsSet_prod_eq_biSup {K : Set X} (hK : IsCompact K) {Y} (l : Filter Y) :
    (𝓝ˢ K) ×ˢ l = ⨆ x ∈ K, 𝓝 x ×ˢ l :=
  le_antisymm (fun s hs ↦ hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun _ hx ↦ prod_mono (nhds_le_nhdsSet hx) le_rfl)

theorem IsCompact.prod_nhdsSet_eq_biSup {K : Set Y} (hK : IsCompact K) {X} (l : Filter X) :
    l ×ˢ (𝓝ˢ K) = ⨆ y ∈ K, l ×ˢ 𝓝 y := by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

/-- If `s : Set (X × Y)` belongs to `l ×ˢ 𝓝 y` for all `y` from a compact set `K`,
then it belongs to `l ×ˢ (𝓝ˢ K)`,
i.e., there exist `t ∈ l` and an open `U ⊇ K` such that `t ×ˢ U ⊆ s`. -/
theorem IsCompact.mem_prod_nhdsSet_of_forall {K : Set Y} {X} {l : Filter X} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ×ˢ 𝓝 y) : s ∈ l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

-- TODO: Is there a way to prove directly the `inf` version and then deduce the `Prod` one ?
-- That would seem a bit more natural.
theorem IsCompact.nhdsSet_inf_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    (𝓝ˢ K) ⊓ l = ⨆ x ∈ K, 𝓝 x ⊓ l := by
  have : ∀ f : Filter X, f ⊓ l = comap (fun x ↦ (x, x)) (f ×ˢ l) := fun f ↦ by
    simpa only [comap_prod] using congrArg₂ (· ⊓ ·) comap_id.symm comap_id.symm
  simp_rw [this, ← comap_iSup, hK.nhdsSet_prod_eq_biSup]

theorem IsCompact.inf_nhdsSet_eq_biSup {K : Set X} (hK : IsCompact K) (l : Filter X) :
    l ⊓ (𝓝ˢ K) = ⨆ x ∈ K, l ⊓ 𝓝 x := by
  simp only [inf_comm l, hK.nhdsSet_inf_eq_biSup]

/-- If `s : Set X` belongs to `𝓝 x ⊓ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ⊓ l`,
i.e., there exist an open `U ⊇ K` and `T ∈ l` such that `U ∩ T ⊆ s`. -/
theorem IsCompact.mem_nhdsSet_inf_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ⊓ l) : s ∈ (𝓝ˢ K) ⊓ l :=
  (hK.nhdsSet_inf_eq_biSup l).symm ▸ by simpa using hs

/-- If `s : Set S` belongs to `l ⊓ 𝓝 x` for all `x` from a compact set `K`,
then it belongs to `l ⊓ (𝓝ˢ K)`,
i.e., there exist `T ∈ l` and an open `U ⊇ K` such that `T ∩ U ⊆ s`. -/
theorem IsCompact.mem_inf_nhdsSet_of_forall {K : Set X} {l : Filter X} {s : Set X}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ⊓ 𝓝 y) : s ∈ l ⊓ 𝓝ˢ K :=
  (hK.inf_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

/-- To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.

Provided for backwards compatibility,
see `IsCompact.mem_prod_nhdsSet_of_forall` for a stronger statement.
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : X} {K : Set Y} (hK : IsCompact K)
    {P : X → Y → Prop} (hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (x₀, y), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y := by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h ↦ h.self_of_nhdsSet

theorem isCompact_empty : IsCompact (∅ : Set X) := fun _f hnf hsf =>
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf

theorem isCompact_singleton {x : X} : IsCompact ({x} : Set X) := fun _ hf hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

theorem Set.Subsingleton.isCompact (hs : s.Subsingleton) : IsCompact s :=
  Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton

theorem Set.Finite.isCompact_biUnion {s : Set ι} {f : ι → Set X} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCompact (f i)) : IsCompact (⋃ i ∈ s, f i) :=
  isCompact_iff_ultrafilter_le_nhds'.2 fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩

theorem Finset.isCompact_biUnion (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  s.finite_toSet.isCompact_biUnion hf

theorem isCompact_accumulate {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (n : ℕ) :
    IsCompact (Accumulate K n) :=
  (finite_le_nat n).isCompact_biUnion fun k _ => hK k

theorem Set.Finite.isCompact_sUnion {S : Set (Set X)} (hf : S.Finite) (hc : ∀ s ∈ S, IsCompact s) :
    IsCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

theorem isCompact_iUnion {ι : Sort*} {f : ι → Set X} [Finite ι] (h : ∀ i, IsCompact (f i)) :
    IsCompact (⋃ i, f i) :=
  (finite_range f).isCompact_sUnion <| forall_mem_range.2 h

@[simp] theorem Set.Finite.isCompact (hs : s.Finite) : IsCompact s :=
  biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton

theorem IsCompact.finite_of_discrete [DiscreteTopology X] (hs : IsCompact s) : s.Finite := by
  have : ∀ x : X, ({x} : Set X) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst

theorem isCompact_iff_finite [DiscreteTopology X] : IsCompact s ↔ s.Finite :=
  ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩

theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption

protected theorem IsCompact.insert (hs : IsCompact s) (a) : IsCompact (insert a s) :=
  isCompact_singleton.union hs

-- TODO: reformulate using `𝓝ˢ`
/-- If `V : ι → Set X` is a decreasing family of closed compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed because `X` is
not assumed to be Hausdorff. See `exists_subset_nhds_of_compact` for version assuming this. -/
theorem exists_subset_nhds_of_isCompact' [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) (hV_closed : ∀ i, IsClosed (V i))
    {U : Set X} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U := by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices ∃ i, V i ⊆ W from this.imp fun i hi => hi.trans hWU
  by_contra! H
  replace H : ∀ i, (V i ∩ Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i ∩ Wᶜ).Nonempty := by
    refine
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun i j => ?_) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine ⟨k, ⟨fun x => ?_, fun x => ?_⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i ⊆ W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction

omit [TopologicalSpace X] in
/--
**Alexander's subbasis theorem**. Suppose `X` is a topological space with a subbasis `S` and `s` is
a subset of `X`. Then `s` is compact if for any open cover of `s` with all elements taken from `S`,
there is a finite subcover.
-/
theorem isCompact_generateFrom [T : TopologicalSpace X]
    {S : Set (Set X)} (hTS : T = generateFrom S) {s : Set X}
    (h : ∀ P ⊆ S, s ⊆ ⋃₀ P → ∃ Q ⊆ P, Q.Finite ∧ s ⊆ ⋃₀ Q) :
    IsCompact s := by
  rw [isCompact_iff_ultrafilter_le_nhds', hTS]
  intro F hsF
  by_contra hF
  have hSF : ∀ x ∈ s, ∃ t, x ∈ t ∧ t ∈ S ∧ t ∉ F := by simpa [nhds_generateFrom] using hF
  choose! U hxU hSU hUF using hSF
  obtain ⟨Q, hQU, hQ, hsQ⟩ := h (U '' s) (by simpa [Set.subset_def])
    (fun x hx ↦ Set.mem_sUnion_of_mem (hxU _ hx) (by aesop))
  have : ∀ s ∈ Q, s ∉ F := fun s hsQ ↦ (hQU hsQ).choose_spec.2 ▸ hUF _ (hQU hsQ).choose_spec.1
  have hQF : ⋂₀ (compl '' Q) ∈ F.sets := by simpa [Filter.biInter_mem hQ, F.compl_mem_iff_notMem]
  have : ⋃₀ Q ∉ F := by
    simpa [-Set.sInter_image, ← Set.compl_sUnion, hsQ, F.compl_mem_iff_notMem] using hQF
  exact this (F.mem_of_superset hsF hsQ)

namespace Filter

theorem hasBasis_cocompact : (cocompact X).HasBasis IsCompact compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isCompact_empty⟩

theorem mem_cocompact : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ tᶜ ⊆ s :=
  hasBasis_cocompact.mem_iff

theorem mem_cocompact' : s ∈ cocompact X ↔ ∃ t, IsCompact t ∧ sᶜ ⊆ t :=
  mem_cocompact.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

theorem _root_.IsCompact.compl_mem_cocompact (hs : IsCompact s) : sᶜ ∈ Filter.cocompact X :=
  hasBasis_cocompact.mem_of_mem hs

theorem cocompact_le_cofinite : cocompact X ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact

theorem cocompact_eq_cofinite (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    cocompact X = cofinite := by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]

/-- A filter is disjoint from the cocompact filter if and only if it contains a compact set. -/
theorem disjoint_cocompact_left (f : Filter X) :
    Disjoint (Filter.cocompact X) f ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_left, compl_compl]
  tauto

/-- A filter is disjoint from the cocompact filter if and only if it contains a compact set. -/
theorem disjoint_cocompact_right (f : Filter X) :
    Disjoint f (Filter.cocompact X) ↔ ∃ K ∈ f, IsCompact K := by
  simp_rw [hasBasis_cocompact.disjoint_iff_right, compl_compl]
  tauto

theorem Tendsto.isCompact_insert_range_of_cocompact {f : X → Y} {y}
    (hf : Tendsto f (cocompact X) (𝓝 y)) (hfc : Continuous f) : IsCompact (insert y (range f)) := by
  intro l hne hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩

theorem Tendsto.isCompact_insert_range_of_cofinite {f : ι → X} {x} (hf : Tendsto f cofinite (𝓝 x)) :
    IsCompact (insert x (range f)) := by
  letI : TopologicalSpace ι := ⊥; haveI h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology

theorem Tendsto.isCompact_insert_range {f : ℕ → X} {x} (hf : Tendsto f atTop (𝓝 x)) :
    IsCompact (insert x (range f)) :=
  Filter.Tendsto.isCompact_insert_range_of_cofinite <| Nat.cofinite_eq_atTop.symm ▸ hf

theorem hasBasis_coclosedCompact :
    (Filter.coclosedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

/-- A set belongs to `coclosedCompact` if and only if the closure of its complement is compact. -/
theorem mem_coclosedCompact_iff :
    s ∈ coclosedCompact X ↔ IsCompact (closure sᶜ) := by
  refine hasBasis_coclosedCompact.mem_iff.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t, ⟨htcl, htco⟩, hst⟩
    exact htco.of_isClosed_subset isClosed_closure <|
      closure_minimal (compl_subset_comm.2 hst) htcl
  · exact ⟨closure sᶜ, ⟨isClosed_closure, h⟩, compl_subset_comm.2 subset_closure⟩

/-- Complement of a set belongs to `coclosedCompact` if and only if its closure is compact. -/
theorem compl_mem_coclosedCompact : sᶜ ∈ coclosedCompact X ↔ IsCompact (closure s) := by
  rw [mem_coclosedCompact_iff, compl_compl]

theorem cocompact_le_coclosedCompact : cocompact X ≤ coclosedCompact X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

end Filter

theorem IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedCompact X :=
  hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩

namespace Bornology

variable (X) in
/-- Sets that are contained in a compact set form a bornology. Its `cobounded` filter is
`Filter.cocompact`. See also `Bornology.relativelyCompact` the bornology of sets with compact
closure. -/
def inCompact : Bornology X where
  cobounded := Filter.cocompact X
  le_cofinite := Filter.cocompact_le_cofinite

theorem inCompact.isBounded_iff : @IsBounded _ (inCompact X) s ↔ ∃ t, IsCompact t ∧ s ⊆ t := by
  change sᶜ ∈ Filter.cocompact X ↔ _
  rw [Filter.mem_cocompact]
  simp

end Bornology

/-- If `s` and `t` are compact sets, then the set neighborhoods filter of `s ×ˢ t`
is the product of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_prod_le`. -/
theorem IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

theorem nhdsSet_prod_le_of_disjoint_cocompact {f : Filter Y} (hs : IsCompact s)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝ˢ s ×ˢ f ≤ 𝓝ˢ (s ×ˢ Set.univ) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    𝓝ˢ s ×ˢ f
    _ ≤ 𝓝ˢ s ×ˢ 𝓟 K        := Filter.prod_mono_right _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ s ×ˢ 𝓝ˢ K       := Filter.prod_mono_right _ principal_le_nhdsSet
    _ = 𝓝ˢ (s ×ˢ K)         := (hs.nhdsSet_prod_eq hK).symm
    _ ≤ 𝓝ˢ (s ×ˢ Set.univ)  := nhdsSet_mono (prod_mono_right le_top)

theorem prod_nhdsSet_le_of_disjoint_cocompact {t : Set Y} {f : Filter X} (ht : IsCompact t)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝ˢ t ≤ 𝓝ˢ (Set.univ ×ˢ t) := by
  obtain ⟨K, hKf, hK⟩ := (disjoint_cocompact_right f).mp hf
  calc
    f ×ˢ 𝓝ˢ t
    _ ≤ (𝓟 K) ×ˢ 𝓝ˢ t      := Filter.prod_mono_left _ (Filter.le_principal_iff.mpr hKf)
    _ ≤ 𝓝ˢ K ×ˢ 𝓝ˢ t       := Filter.prod_mono_left _ principal_le_nhdsSet
    _ = 𝓝ˢ (K ×ˢ t)         := (hK.nhdsSet_prod_eq ht).symm
    _ ≤ 𝓝ˢ (Set.univ ×ˢ t)  := nhdsSet_mono (prod_mono_left le_top)

theorem nhds_prod_le_of_disjoint_cocompact {f : Filter Y} (x : X)
    (hf : Disjoint f (Filter.cocompact Y)) :
    𝓝 x ×ˢ f ≤ 𝓝ˢ ({x} ×ˢ Set.univ) := by
  simpa using nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton hf

theorem prod_nhds_le_of_disjoint_cocompact {f : Filter X} (y : Y)
    (hf : Disjoint f (Filter.cocompact X)) :
    f ×ˢ 𝓝 y ≤ 𝓝ˢ (Set.univ ×ˢ {y}) := by
  simpa using prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton hf

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`.

See also `IsCompact.nhdsSet_prod_eq`. -/
theorem generalized_tube_lemma (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by
  rw [← hn.mem_nhdsSet, hs.nhdsSet_prod_eq ht,
    ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩

/-- A relative version of `IsCompact.nhdsSet_prod_eq`: if `s` and `t` are compact sets,
then the neighborhoods filter of `s ×ˢ t` within `s' ×ˢ t'` is the product of the neighborhoods
filters of `s` and `t` within `s'` and `t'`.

For general sets, only the `≤` inequality holds, see `nhdsSetWithin_prod_le`. -/
lemma IsCompact.nhdsSetWithin_prod_eq {s s' : Set X} {t t' : Set Y} (hs : IsCompact s)
    (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

open Topology Set in
/-- A variant of `generalized_tube_lemma` in terms of `nhdsSetWithin`. -/
lemma generalized_tube_lemma' {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)) :
    ∃ u ∈ 𝓝ˢ[s'] s, ∃ v ∈ 𝓝ˢ[t'] t, u ×ˢ v ⊆ n := by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

open Topology Set in
/-- A variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
lemma generalized_tube_lemma_left {s s' : Set X} (hs : IsCompact s) {t : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)) : ∃ u ∈ 𝓝ˢ[s'] s, u ×ˢ t ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx ↦ hx.1 _ hx.2⟩

open Topology Set in
/-- A variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
lemma generalized_tube_lemma_right {s : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t)
    {n : Set (X × Y)} (hn : n ∈ 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)) : ∃ u ∈ 𝓝ˢ[t'] t, s ×ˢ u ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

-- see Note [lower instance priority]
instance (priority := 10) Subsingleton.compactSpace [Subsingleton X] : CompactSpace X :=
  ⟨subsingleton_univ.isCompact⟩

theorem isCompact_univ_iff : IsCompact (univ : Set X) ↔ CompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X) :=
  h.isCompact_univ

theorem exists_clusterPt_of_compactSpace [CompactSpace X] (f : Filter X) [NeBot f] :
    ∃ x, ClusterPt x f := by
  simpa using isCompact_univ (show f ≤ 𝓟 univ by simp)

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace X] (F : Ultrafilter X) : ↑F ≤ 𝓝 F.lim := by
  rcases isCompact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩
  exact le_nhds_lim ⟨x, h⟩

theorem CompactSpace.elim_nhds_subcover [CompactSpace X] (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = ⊤ := by
  obtain ⟨t, -, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  exact ⟨t, top_unique s⟩

theorem compactSpace_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (t : ι → Set X), (∀ i, IsClosed (t i)) → ⋂ i, t i = ∅ →
      ∃ u : Finset ι, ⋂ i ∈ u, t i = ∅) :
    CompactSpace X where
  isCompact_univ := isCompact_of_finite_subfamily_closed fun t => by simpa using h t

/--
Given a family of closed sets `t i` in a compact space, if they satisfy the Finite Intersection
Property, then the intersection of all `t i` is nonempty.
-/
lemma CompactSpace.iInter_nonempty {ι : Type v} [CompactSpace X] {t : ι → Set X}
    (htc : ∀ i, IsClosed (t i))
    (hst : ∀ s : Finset ι, (⋂ i ∈ s, t i).Nonempty) :
    (⋂ i, t i).Nonempty := by
  simpa using IsCompact.inter_iInter_nonempty isCompact_univ t htc (by simpa using hst)

omit [TopologicalSpace X] in
/--
The `CompactSpace` version of **Alexander's subbasis theorem**. If `X` is a topological space with a
subbasis `S`, then `X` is compact if for any open cover of `X` all of whose elements belong to `S`,
there is a finite subcover.
-/
theorem compactSpace_generateFrom [T : TopologicalSpace X] {S : Set (Set X)}
    (hTS : T = generateFrom S) (h : ∀ P ⊆ S, ⋃₀ P = univ → ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = univ) :
    CompactSpace X := by
  rw [← isCompact_univ_iff]
  exact isCompact_generateFrom hTS <| by simpa

theorem IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)

/-- If a filter has a unique cluster point `y` in a compact topological space,
then the filter is less than or equal to `𝓝 y`. -/
lemma le_nhds_of_unique_clusterPt [CompactSpace X] {l : Filter X} {y : X}
    (h : ∀ x, ClusterPt x l → x = y) : l ≤ 𝓝 y :=
  isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ ↦ h x

/-- If `y` is a unique `MapClusterPt` for `f` along `l`
and the codomain of `f` is a compact space,
then `f` tends to `𝓝 y` along `l`. -/
lemma tendsto_nhds_of_unique_mapClusterPt [CompactSpace X] {Y} {l : Filter Y} {y : X} {f : Y → X}
    (h : ∀ x, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  le_nhds_of_unique_clusterPt h

lemma noncompact_univ (X : Type*) [TopologicalSpace X] [NoncompactSpace X] :
    ¬IsCompact (univ : Set X) :=
  NoncompactSpace.noncompact_univ

theorem IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact s) : s ≠ univ := fun h =>
  noncompact_univ X (h ▸ hs)

instance [NoncompactSpace X] : NeBot (Filter.cocompact X) := by
  refine Filter.hasBasis_cocompact.neBot_iff.2 fun hs => ?_
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ X

@[simp]
theorem Filter.cocompact_eq_bot [CompactSpace X] : Filter.cocompact X = ⊥ :=
  Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩

instance [NoncompactSpace X] : NeBot (Filter.coclosedCompact X) :=
  neBot_of_le Filter.cocompact_le_coclosedCompact

theorem noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact X)) : NoncompactSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

theorem Filter.cocompact_neBot_iff : NeBot (Filter.cocompact X) ↔ NoncompactSpace X :=
  ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩

theorem not_compactSpace_iff : ¬CompactSpace X ↔ NoncompactSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

instance : NoncompactSpace ℤ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

-- Note: We can't make this into an instance because it loops with `Finite.compactSpace`.
/-- A compact discrete space is finite. -/
theorem finite_of_compact_of_discrete [CompactSpace X] [DiscreteTopology X] : Finite X :=
  Finite.of_finite_univ <| isCompact_univ.finite_of_discrete

lemma Set.Infinite.exists_accPt_cofinite_inf_principal_of_subset_isCompact
    {K : Set X} (hs : s.Infinite) (hK : IsCompact K) (hsub : s ⊆ K) :
    ∃ x ∈ K, AccPt x (cofinite ⊓ 𝓟 s) :=
  (@hK _ hs.cofinite_inf_principal_neBot (inf_le_right.trans <| principal_mono.2 hsub)).imp
    fun x hx ↦ by rwa [accPt_iff_clusterPt, inf_comm, inf_right_comm,
      (finite_singleton _).cofinite_inf_principal_compl]

lemma Set.Infinite.exists_accPt_of_subset_isCompact {K : Set X} (hs : s.Infinite)
    (hK : IsCompact K) (hsub : s ⊆ K) : ∃ x ∈ K, AccPt x (𝓟 s) :=
  let ⟨x, hxK, hx⟩ := hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact hK hsub
  ⟨x, hxK, hx.mono inf_le_right⟩

lemma Set.Infinite.exists_accPt_cofinite_inf_principal [CompactSpace X] (hs : s.Infinite) :
    ∃ x, AccPt x (cofinite ⊓ 𝓟 s) := by
  simpa only [mem_univ, true_and]
    using hs.exists_accPt_cofinite_inf_principal_of_subset_isCompact isCompact_univ s.subset_univ

lemma Set.Infinite.exists_accPt_principal [CompactSpace X] (hs : s.Infinite) : ∃ x, AccPt x (𝓟 s) :=
  hs.exists_accPt_cofinite_inf_principal.imp fun _x hx ↦ hx.mono inf_le_right

theorem exists_nhds_ne_neBot (X : Type*) [TopologicalSpace X] [CompactSpace X] [Infinite X] :
    ∃ z : X, (𝓝[≠] z).NeBot := by
  simpa [AccPt] using (@infinite_univ X _).exists_accPt_principal

theorem finite_cover_nhds_interior [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

theorem finite_cover_nhds [CompactSpace X] {U : X → Set X} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
  ⟨t, univ_subset_iff.1 <| ht.symm.subset.trans <| iUnion₂_mono fun _ _ => interior_subset⟩

/-- The comap of the cocompact filter on `Y` by a continuous function `f : X → Y` is less than or
equal to the cocompact filter on `X`.
This is a reformulation of the fact that images of compact sets are compact. -/
theorem Filter.comap_cocompact_le {f : X → Y} (hf : Continuous f) :
    (Filter.cocompact Y).comap f ≤ Filter.cocompact X := by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

/-- If a filter is disjoint from the cocompact filter, so is its image under any continuous
function. -/
theorem disjoint_map_cocompact {g : X → Y} {f : Filter X} (hg : Continuous g)
    (hf : Disjoint f (Filter.cocompact X)) : Disjoint (map g f) (Filter.cocompact Y) := by
  rw [← Filter.disjoint_comap_iff_map, disjoint_iff_inf_le]
  calc
    f ⊓ (comap g (cocompact Y))
    _ ≤ f ⊓ Filter.cocompact X := inf_le_inf_left f (Filter.comap_cocompact_le hg)
    _ = ⊥ := disjoint_iff.mp hf

theorem isCompact_range [CompactSpace X] {f : X → Y} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf

theorem isCompact_diagonal [CompactSpace X] : IsCompact (diagonal X) :=
  @range_diag X ▸ isCompact_range (continuous_id.prodMk continuous_id)

theorem exists_subset_nhds_of_compactSpace [CompactSpace X] [Nonempty ι]
    {V : ι → Set X} (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is compact
  if and only if `s` is compact. -/
theorem Topology.IsInducing.isCompact_iff {f : X → Y} (hf : IsInducing f) :
    IsCompact s ↔ IsCompact (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is compact
if and only if `s` is compact. -/
theorem Topology.IsEmbedding.isCompact_iff {f : X → Y} (hf : IsEmbedding f) :
    IsCompact s ↔ IsCompact (f '' s) := hf.isInducing.isCompact_iff

/-- The preimage of a compact set under an inducing map is a compact set. -/
theorem Topology.IsInducing.isCompact_preimage (hf : IsInducing f) (hf' : IsClosed (range f))
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

lemma Topology.IsInducing.isCompact_preimage_iff {f : X → Y} (hf : IsInducing f) {K : Set Y}
    (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) ↔ IsCompact K := by
  rw [hf.isCompact_iff, image_preimage_eq_of_subset Kf]

/-- The preimage of a compact set in the image of an inducing map is compact. -/
lemma Topology.IsInducing.isCompact_preimage' (hf : IsInducing f) {K : Set Y}
    (hK : IsCompact K) (Kf : K ⊆ range f) : IsCompact (f ⁻¹' K) :=
  (hf.isCompact_preimage_iff Kf).2 hK

/-- The preimage of a compact set under a closed embedding is a compact set. -/
theorem Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

/-- A closed embedding is proper, i.e., inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `IsClosedEmbedding.isCompact_preimage`. -/
theorem Topology.IsClosedEmbedding.tendsto_cocompact (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.cocompact X) (Filter.cocompact Y) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact

/-- Sets of subtype are compact iff the image under a coercion is. -/
theorem Subtype.isCompact_iff {p : X → Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff

theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]

theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff

theorem IsCompact.finite (hs : IsCompact s) (hs' : DiscreteTopology s) : s.Finite :=
  finite_coe_iff.mp (@finite_of_compact_of_discrete _ _ (isCompact_iff_compactSpace.mp hs) hs')

theorem exists_nhds_ne_inf_principal_neBot (hs : IsCompact s) (hs' : s.Infinite) :
    ∃ z ∈ s, (𝓝[≠] z ⊓ 𝓟 s).NeBot :=
  hs'.exists_accPt_of_subset_isCompact hs Subset.rfl

protected theorem Topology.IsClosedEmbedding.noncompactSpace [NoncompactSpace X] {f : X → Y}
    (hf : IsClosedEmbedding f) : NoncompactSpace Y :=
  noncompactSpace_of_neBot hf.tendsto_cocompact.neBot

protected theorem Topology.IsClosedEmbedding.compactSpace [h : CompactSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : CompactSpace X :=
  ⟨by rw [hf.isInducing.isCompact_iff, image_univ]; exact hf.isClosed_range.isCompact⟩

theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x ∈ s, hx : map Prod.fst f.1 ≤ 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y ∈ t, hy : map Prod.snd f.1 ≤ 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy

/-- Finite topological spaces are compact. -/
instance (priority := 100) Finite.compactSpace [Finite X] : CompactSpace X where
  isCompact_univ := finite_univ.isCompact

instance ULift.compactSpace [CompactSpace X] : CompactSpace (ULift.{v} X) :=
  IsClosedEmbedding.uliftDown.compactSpace

/-- The product of two compact spaces is compact. -/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X × Y) :=
  ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

/-- The disjoint union of two compact spaces is compact. -/
instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X ⊕ Y) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

instance {X : ι → Type*} [Finite ι] [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] :
    CompactSpace (Σ i, X i) := by
  refine ⟨?_⟩
  rw [Sigma.univ]
  exact isCompact_iUnion fun i => isCompact_range continuous_sigmaMk

lemma Set.isCompact_sigma {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {s : Set ι}
    {t : ∀ i, Set (X i)} (hs : s.Finite) (ht : ∀ i ∈ s, IsCompact (t i)) :
    IsCompact (s.sigma t) := by
  rw [Set.sigma_eq_biUnion]
  exact hs.isCompact_biUnion fun i hi ↦ (ht i hi).image continuous_sigmaMk

lemma IsCompact.sigma_exists_finite_sigma_eq {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (u : Set (Σ i, X i)) (hu : IsCompact u) :
    ∃ (s : Set ι) (t : ∀ i, Set (X i)), s.Finite ∧ (∀ i, IsCompact (t i)) ∧ s.sigma t = u := by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι ↦ Sigma.mk i '' (Sigma.mk i ⁻¹' Set.univ))
    (fun i ↦ isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx ↦ (by simp)
  use s, fun i ↦ Sigma.mk i ⁻¹' u, s.finite_toSet, fun i ↦ ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    simp_all

/-- The coproduct of the cocompact filters on two topological spaces is the cocompact filter on
their product. -/
theorem Filter.coprod_cocompact :
    (Filter.cocompact X).coprod (Filter.cocompact Y) = Filter.cocompact (X × Y) := by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK ↦ ?_
    rw [← univ_prod, ← prod_univ, ← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact

theorem Prod.noncompactSpace_iff :
    NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ Nonempty Y ∨ Nonempty X ∧ NoncompactSpace Y := by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_left [NoncompactSpace X] [Nonempty Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_right [Nonempty X] [NoncompactSpace Y] :
    NoncompactSpace (X × Y) :=
  Prod.noncompactSpace_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

section Tychonoff

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- **Tychonoff's theorem**: product of compact sets is compact. -/
theorem isCompact_pi_infinite {s : ∀ i, Set (X i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, le_pi, le_principal_iff]
  intro h f hfs
  have : ∀ i : ι, ∃ x, x ∈ s i ∧ Tendsto (Function.eval i) f (𝓝 x) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose x hx using this
  exact ⟨x, fun i => (hx i).left, fun i => (hx i).right⟩

/-- **Tychonoff's theorem** formulated using `Set.pi`: product of compact sets is compact. -/
theorem isCompact_univ_pi {s : ∀ i, Set (X i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact (pi univ s) := by
  convert isCompact_pi_infinite h
  simp only [← mem_univ_pi, setOf_mem_eq]

instance Pi.compactSpace [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩

instance Function.compactSpace [CompactSpace Y] : CompactSpace (ι → Y) :=
  Pi.compactSpace

lemma Pi.isCompact_iff_of_isClosed {s : Set (Π i, X i)} (hs : IsClosed s) :
    IsCompact s ↔ ∀ i, IsCompact (eval i '' s) := by
  constructor <;> intro H
  · exact fun i ↦ H.image <| continuous_apply i
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H) hs (subset_pi_eval_image univ s)

protected lemma Pi.exists_compact_superset_iff {s : Set (Π i, X i)} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ ∀ i, ∃ Ki, IsCompact Ki ∧ s ⊆ eval i ⁻¹' Ki := by
  constructor
  · intro ⟨K, hK, hsK⟩ i
    exact ⟨eval i '' K, hK.image <| continuous_apply i, hsK.trans <| K.subset_preimage_image _⟩
  · intro H
    choose K hK hsK using H
    exact ⟨pi univ K, isCompact_univ_pi hK, fun _ hx i _ ↦ hsK i hx⟩

/-- **Tychonoff's theorem** formulated in terms of filters: `Filter.cocompact` on an indexed product
type `Π d, X d` the `Filter.coprodᵢ` of filters `Filter.cocompact` on `X d`. -/
theorem Filter.coprodᵢ_cocompact {X : ι → Type*} [∀ d, TopologicalSpace (X d)] :
    (Filter.coprodᵢ fun d => Filter.cocompact (X d)) = Filter.cocompact (∀ d, X d) := by
  refine le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) ?_
  refine compl_surjective.forall.2 fun s H => ?_
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩

end Tychonoff

instance Quot.compactSpace {r : X → X → Prop} [CompactSpace X] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩

instance Quotient.compactSpace {s : Setoid X} [CompactSpace X] : CompactSpace (Quotient s) :=
  Quot.compactSpace

theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ V : Set X, V ⊆ S ∧ V.Nonempty ∧ IsClosed V ∧
      ∀ V' : Set X, V' ⊆ V → V'.Nonempty → IsClosed V' → V' = V := by
  let opens := { U : Set X | Sᶜ ⊆ U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        haveI : Nonempty { U // U ∈ c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine ⟨⟨?_, ?_, ?_⟩, fun U hU _ hx => ⟨U, hU, hx⟩⟩
        · exact fun _ hx => ⟨U₀, hU₀, U₀compl hx⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U ∈ c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, not_and, Set.mem_iInter, Subtype.forall,
              mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, ?_⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  obtain ⟨Uc, Uo, Ucne⟩ := h.prop
  refine ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, ?_⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine h.eq_of_ge ⟨?_, isOpen_compl_iff.mpr V'cls, ?_⟩ (subset_compl_comm.2 V'sub)
    · exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    · simp only [compl_compl, V'ne]
  rw [← this, compl_compl]

end Compact
