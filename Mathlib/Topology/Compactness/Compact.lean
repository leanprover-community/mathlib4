/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Bases
import Mathlib.Data.Set.Accumulate
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.LocallyFinite
/-!
# Compact sets and compact spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsCompact`: a set such that each open cover has a finite subcover. This is defined in mathlib
  using filters. The main property of a compact set is `IsCompact.elim_finite_subcover`.
* `CompactSpace`: typeclass stating that the whole space is a compact set.
* `NoncompactSpace`: a space that is not a compact space.

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.
-/
open Set Filter Topology TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*}

variable [TopologicalSpace α] [TopologicalSpace β] {s t : Set α}

-- compact sets
section Compact

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set α) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a f
#align is_compact IsCompact

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 a ⊓ f`, `a ∈ s`. -/
theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter α} (hf : ∀ a ∈ s, sᶜ ∈ 𝓝 a ⊓ f) :
    sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right
#align is_compact.compl_mem_sets IsCompact.compl_mem_sets

/-- The complement to a compact set belongs to a filter `f` if each `a ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter α}
    (hf : ∀ a ∈ s, ∃ t ∈ 𝓝[s] a, tᶜ ∈ f) : sᶜ ∈ f := by
  refine' hs.compl_mem_sets fun a ha => _
  rcases hf a ha with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)
#align is_compact.compl_mem_sets_of_nhds_within IsCompact.compl_mem_sets_of_nhdsWithin

/-- If `p : Set α → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsCompact.induction_on {s : Set α} (hs : IsCompact s) {p : Set α → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter α :=
    { sets := { t | p tᶜ }
      univ_sets := by simpa
      sets_of_superset := fun ht₁ ht => hmono (compl_subset_compl.2 ht) ht₁
      inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion ht₁ ht₂] }
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa using hnhds)
  rwa [← compl_compl s]
#align is_compact.induction_on IsCompact.induction_on

/-- The intersection of a compact set and a closed set is a compact set. -/
theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) := by
  intro f hnf hstf
  obtain ⟨a, hsa, ha⟩ : ∃ a ∈ s, ClusterPt a f :=
    hs (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _)))
  have : a ∈ t := ht.mem_of_nhdsWithin_neBot <|
    ha.mono <| le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))
  exact ⟨a, ⟨hsa, this⟩, ha⟩
#align is_compact.inter_right IsCompact.inter_right

/-- The intersection of a closed set and a compact set is a compact set. -/
theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs
#align is_compact.inter_left IsCompact.inter_left

/-- The set difference of a compact set and an open set is a compact set. -/
theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)
#align is_compact.diff IsCompact.diff

/-- A closed subset of a compact set is a compact set. -/
theorem IsCompact.of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht
#align is_compact_of_is_closed_subset IsCompact.of_isClosed_subset

theorem IsCompact.image_of_continuousOn {f : α → β} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ClusterPt a (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  haveI := ha.neBot
  use f a, mem_image_of_mem f has
  have : Tendsto f (𝓝 a ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f a) ⊓ l) := by
    convert (hf a has).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot
#align is_compact.image_of_continuous_on IsCompact.image_of_continuousOn

theorem IsCompact.image {f : α → β} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
#align is_compact.image IsCompact.image

theorem IsCompact.adherence_nhdset {f : Filter α} (hs : IsCompact s) (hf₂ : f ≤ 𝓟 s)
    (ht₁ : IsOpen t) (ht₂ : ∀ a ∈ s, ClusterPt a f → a ∈ t) : t ∈ f :=
  Classical.by_cases mem_of_eq_bot fun (this : f ⊓ 𝓟 tᶜ ≠ ⊥) =>
    let ⟨a, ha, (hfa : ClusterPt a <| f ⊓ 𝓟 tᶜ)⟩ := @hs _ ⟨this⟩ <| inf_le_of_left_le hf₂
    have : a ∈ t := ht₂ a ha hfa.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] a := inter_mem_nhdsWithin _ (IsOpen.mem_nhds ht₁ this)
    have A : 𝓝[tᶜ] a = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] a ≠ ⊥ := hfa.of_inf_right.ne
    absurd A this
#align is_compact.adherence_nhdset IsCompact.adherence_nhdset

theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → ∃ a ∈ s, ↑f ≤ 𝓝 a := by
  refine' (forall_neBot_le_iff _).trans _
  · rintro f g hle ⟨a, has, haf⟩
    exact ⟨a, has, haf.mono hle⟩
  · simp only [Ultrafilter.clusterPt_iff]
#align is_compact_iff_ultrafilter_le_nhds isCompact_iff_ultrafilter_le_nhds

alias ⟨IsCompact.ultrafilter_le_nhds, _⟩ := isCompact_iff_ultrafilter_le_nhds
#align is_compact.ultrafilter_le_nhds IsCompact.ultrafilter_le_nhds

theorem isCompact_iff_ultrafilter_le_nhds' :
    IsCompact s ↔ ∀ f : Ultrafilter α, s ∈ f → ∃ a ∈ s, ↑f ≤ 𝓝 a := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff, Ultrafilter.mem_coe]

alias ⟨IsCompact.ultrafilter_le_nhds', _⟩ := isCompact_iff_ultrafilter_le_nhds'

/-- If a compact set belongs to a filter and this filter has a unique cluster point `y` in this set,
then the filter is less than or equal to `𝓝 y`. -/
lemma IsCompact.le_nhds_of_unique_clusterPt (hs : IsCompact s) {l : Filter α} {y : α}
    (hmem : s ∈ l) (h : ∀ x ∈ s, ClusterPt x l → x = y) : l ≤ 𝓝 y := by
  refine le_iff_ultrafilter.2 fun f hf ↦ ?_
  rcases hs.ultrafilter_le_nhds' f (hf hmem) with ⟨x, hxs, hx⟩
  convert ← hx
  exact h x hxs (.mono (.of_le_nhds hx) hf)

/-- If values of `f : β → α` belong to a compact set `s` eventually along a filter `l`
and `y` is a unique `MapClusterPt` for `f` along `l` in `s`,
then `f` tends to `𝓝 y` along `l`. -/
lemma IsCompact.tendsto_nhds_of_unique_mapClusterPt {l : Filter β} {y : α} {f : β → α}
    (hs : IsCompact s) (hmem : ∀ᶠ x in l, f x ∈ s) (h : ∀ x ∈ s, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  hs.le_nhds_of_unique_clusterPt (mem_map.2 hmem) h

/-- For every open directed cover of a compact set, there exists a single element of the
cover which itself includes the set. -/
theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (U : ι → Set α) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) :
    ∃ i, s ⊆ U i :=
  hι.elim fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun _ _ hs ⟨i, hi⟩ => ⟨i, hs.trans hi⟩)
      (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (Subset.trans hi hki) (Subset.trans hj hkj)⟩)
      fun _x hx =>
      let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
      ⟨U i, mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, Subset.refl _⟩
#align is_compact.elim_directed_cover IsCompact.elim_directed_cover

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hsU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)
#align is_compact.elim_finite_subcover IsCompact.elim_finite_subcover

theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : ∀ x ∈ s, Set α)
    (hU : ∀ x (hx : x ∈ s), U x ‹x ∈ s› ∈ 𝓝 x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
  (hs.elim_finite_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior) fun x hx =>
        mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 <| hU _ _⟩).imp
    fun _t ht => ht.trans <| iUnion₂_mono fun _ _ => interior_subset
#align is_compact.elim_nhds_subcover' IsCompact.elim_nhds_subcover'

theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : α → Set α) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ t : Finset α, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
  let ⟨t, ht⟩ := hs.elim_nhds_subcover' (fun x _ => U x) hU
  ⟨t.image (↑), fun x hx =>
    let ⟨y, _, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by rwa [Finset.set_biUnion_finset_image]⟩
#align is_compact.elim_nhds_subcover IsCompact.elim_nhds_subcover

/-- The neighborhood filter of a compact set is disjoint with a filter `l` if and only if the
neighborhood filter of each point of this set is disjoint with `l`. -/
theorem IsCompact.disjoint_nhdsSet_left {l : Filter α} (hs : IsCompact s) :
    Disjoint (𝓝ˢ s) l ↔ ∀ x ∈ s, Disjoint (𝓝 x) l := by
  refine' ⟨fun h x hx => h.mono_left <| nhds_le_nhdsSet hx, fun H => _⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂, biInter_finset_mem]
  exact fun x hx => hUl x (hts x hx)
#align is_compact.disjoint_nhds_set_left IsCompact.disjoint_nhdsSet_left

/-- A filter `l` is disjoint with the neighborhood filter of a compact set if and only if it is
disjoint with the neighborhood filter of each point of this set. -/
theorem IsCompact.disjoint_nhdsSet_right {l : Filter α} (hs : IsCompact s) :
    Disjoint l (𝓝ˢ s) ↔ ∀ x ∈ s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left
#align is_compact.disjoint_nhds_set_right IsCompact.disjoint_nhdsSet_right

-- porting note: todo: reformulate using `Disjoint`
/-- For every directed family of closed sets whose intersection avoids a compact set,
there exists a single element of the family which itself avoids this compact set. -/
theorem IsCompact.elim_directed_family_closed {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s)
    (Z : ι → Set α) (hZc : ∀ i, IsClosed (Z i)) (hsZ : (s ∩ ⋂ i, Z i) = ∅)
    (hdZ : Directed (· ⊇ ·) Z) : ∃ i : ι, s ∩ Z i = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_directed_cover (compl ∘ Z) (fun i => (hZc i).isOpen_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_iUnion, exists_prop,
          mem_inter_iff, not_and, iff_self_iff, mem_iInter, mem_compl_iff] using hsZ)
      (hdZ.mono_comp _ fun _ _ => compl_subset_compl.mpr)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_iUnion, exists_prop,
      mem_inter_iff, not_and, iff_self_iff, mem_iInter, mem_compl_iff] using ht⟩
#align is_compact.elim_directed_family_closed IsCompact.elim_directed_family_closed

-- porting note: todo: reformulate using `Disjoint`
/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
theorem IsCompact.elim_finite_subfamily_closed {s : Set α} {ι : Type v} (hs : IsCompact s)
    (Z : ι → Set α) (hZc : ∀ i, IsClosed (Z i)) (hsZ : (s ∩ ⋂ i, Z i) = ∅) :
    ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅ :=
  hs.elim_directed_family_closed _ (fun t ↦ isClosed_biInter fun _ _ ↦ hZc _)
    (by rwa [← iInter_eq_iInter_finset])
    (directed_of_isDirected_le fun _ _ h ↦ biInter_subset_biInter_left h)
#align is_compact.elim_finite_subfamily_closed IsCompact.elim_finite_subfamily_closed

/-- If `s` is a compact set in a topological space `α` and `f : ι → Set α` is a locally finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`. -/
theorem LocallyFinite.finite_nonempty_inter_compact {ι : Type*} {f : ι → Set α}
    (hf : LocallyFinite f) {s : Set α} (hs : IsCompact s) : { i | (f i ∩ s).Nonempty }.Finite := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine' (t.finite_toSet.biUnion fun x _ => hUf x).subset _
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩
#align locally_finite.finite_nonempty_inter_compact LocallyFinite.finite_nonempty_inter_compact

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
theorem IsCompact.inter_iInter_nonempty {s : Set α} {ι : Type v} (hs : IsCompact s) (Z : ι → Set α)
    (hZc : ∀ i, IsClosed (Z i)) (hsZ : ∀ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i).Nonempty) :
    (s ∩ ⋂ i, Z i).Nonempty := by
  contrapose! hsZ
  exact hs.elim_finite_subfamily_closed Z hZc hsZ
#align is_compact.inter_Inter_nonempty IsCompact.inter_iInter_nonempty

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed {ι : Type v} [hι : Nonempty ι]
    (Z : ι → Set α) (hZd : Directed (· ⊇ ·) Z) (hZn : ∀ i, (Z i).Nonempty)
    (hZc : ∀ i, IsCompact (Z i)) (hZcl : ∀ i, IsClosed (Z i)) : (⋂ i, Z i).Nonempty := by
  let i₀ := hι.some
  suffices (Z i₀ ∩ ⋂ i, Z i).Nonempty by
    rwa [inter_eq_right.mpr (iInter_subset _ i₀)] at this
  simp only [nonempty_iff_ne_empty] at hZn ⊢
  apply mt ((hZc i₀).elim_directed_family_closed Z hZcl)
  push_neg
  simp only [← nonempty_iff_ne_empty] at hZn ⊢
  refine' ⟨hZd, fun i => _⟩
  rcases hZd i₀ i with ⟨j, hji₀, hji⟩
  exact (hZn j).mono (subset_inter hji₀ hji)
#align is_compact.nonempty_Inter_of_directed_nonempty_compact_closed IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed (Z : ℕ → Set α)
    (hZd : ∀ i, Z (i + 1) ⊆ Z i) (hZn : ∀ i, (Z i).Nonempty) (hZ0 : IsCompact (Z 0))
    (hZcl : ∀ i, IsClosed (Z i)) : (⋂ i, Z i).Nonempty :=
  have Zmono : Antitone Z := antitone_nat_of_succ_le hZd
  have hZd : Directed (· ⊇ ·) Z := Zmono.directed_ge
  have : ∀ i, Z i ⊆ Z 0 := fun i => Zmono <| zero_le i
  have hZc : ∀ i, IsCompact (Z i) := fun i => hZ0.of_isClosed_subset (hZcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed Z hZd hZn hZc hZcl
#align is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i ∈ b, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b', b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_finite_subcover (fun i => c i : b → Set α) hc₁ hc₂ with ⟨d, hd⟩
  refine' ⟨Subtype.val '' d.toSet, _, d.finite_toSet.image _, _⟩
  · simp
  · rwa [biUnion_image]
#align is_compact.elim_finite_subcover_image IsCompact.elim_finite_subcover_imageₓ

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_of_finite_subcover
    (h : ∀ {ι : Type u} (U : ι → Set α), (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) →
      ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i) :
    IsCompact s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1⟩, fun t ht => ?_⟩
  refine compl_not_mem (le_principal_iff.1 hfs) ?_
  refine mem_of_superset ((biInter_finset_mem t).2 fun x _ => hUf x) ?_
  rw [subset_compl_comm, compl_iInter₂]
  simpa only [compl_compl]
#align is_compact_of_finite_subcover isCompact_of_finite_subcover

-- porting note: todo: reformulate using `Disjoint`
/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem isCompact_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (Z : ι → Set α), (∀ i, IsClosed (Z i)) → (s ∩ ⋂ i, Z i) = ∅ →
      ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅) :
    IsCompact s :=
  isCompact_of_finite_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset, compl_iUnion, disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]
#align is_compact_of_finite_subfamily_closed isCompact_of_finite_subfamily_closed

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set α),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩
#align is_compact_iff_finite_subcover isCompact_iff_finite_subcover

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem isCompact_iff_finite_subfamily_closed :
    IsCompact s ↔ ∀ {ι : Type u} (Z : ι → Set α),
      (∀ i, IsClosed (Z i)) → (s ∩ ⋂ i, Z i) = ∅ → ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅ :=
  ⟨fun hs => hs.elim_finite_subfamily_closed, isCompact_of_finite_subfamily_closed⟩
#align is_compact_iff_finite_subfamily_closed isCompact_iff_finite_subfamily_closed

/-- If `s : Set (α × β)` belongs to `𝓝 x ×ˢ l` for all `x` from a compact set `K`,
then it belongs to `(𝓝ˢ K) ×ˢ l`,
i.e., there exist an open `U ⊇ K` and `t ∈ l` such that `U ×ˢ t ⊆ s`. -/
theorem IsCompact.mem_nhdsSet_prod_of_forall {K : Set α} {l : Filter β} {s : Set (α × β)}
    (hK : IsCompact K) (hs : ∀ x ∈ K, s ∈ 𝓝 x ×ˢ l) : s ∈ (𝓝ˢ K) ×ˢ l := by
  refine hK.induction_on (by simp) (fun t t' ht hs ↦ ?_) (fun t t' ht ht' ↦ ?_) fun x hx ↦ ?_
  · exact prod_mono (nhdsSet_mono ht) le_rfl hs
  · simp [sup_prod, *]
  · rcases ((nhds_basis_opens _).prod l.basis_sets).mem_iff.1 (hs x hx)
      with ⟨⟨u, v⟩, ⟨⟨hx, huo⟩, hv⟩, hs⟩
    refine ⟨u, nhdsWithin_le_nhds (huo.mem_nhds hx), mem_of_superset ?_ hs⟩
    exact prod_mem_prod (huo.mem_nhdsSet.2 Subset.rfl) hv

theorem IsCompact.nhdsSet_prod_eq_biSup {K : Set α} (hK : IsCompact K) (l : Filter β) :
    (𝓝ˢ K) ×ˢ l = ⨆ x ∈ K, 𝓝 x ×ˢ l :=
  le_antisymm (fun s hs ↦ hK.mem_nhdsSet_prod_of_forall <| by simpa using hs)
    (iSup₂_le fun x hx ↦ prod_mono (nhds_le_nhdsSet hx) le_rfl)

theorem IsCompact.prod_nhdsSet_eq_biSup {K : Set β} (hK : IsCompact K) (l : Filter α) :
    l ×ˢ (𝓝ˢ K) = ⨆ y ∈ K, l ×ˢ 𝓝 y := by
  simp only [prod_comm (f := l), hK.nhdsSet_prod_eq_biSup, map_iSup]

/-- If `s : Set (α × β)` belongs to `l ×ˢ 𝓝 y` for all `y` from a compact set `K`,
then it belongs to `l ×ˢ (𝓝ˢ K)`,
i.e., there exist `t ∈ l` and an open `U ⊇ K` such that `t ×ˢ U ⊆ s`. -/
theorem IsCompact.mem_prod_nhdsSet_of_forall {K : Set β} {l : Filter α} {s : Set (α × β)}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ×ˢ 𝓝 y) : s ∈ l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

/-- To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.

Provided for backwards compatibility,
see `IsCompact.mem_prod_nhdsSet_of_forall` for a stronger statement.
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : α} {K : Set β} (hK : IsCompact K)
    {P : α → β → Prop} (hP : ∀ y ∈ K, ∀ᶠ z : α × β in 𝓝 (x₀, y), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y := by
  simp only [nhds_prod_eq, ← eventually_iSup, ← hK.prod_nhdsSet_eq_biSup] at hP
  exact hP.curry.mono fun _ h ↦ h.self_of_nhdsSet
#align is_compact.eventually_forall_of_forall_eventually IsCompact.eventually_forall_of_forall_eventually

@[simp]
theorem isCompact_empty : IsCompact (∅ : Set α) := fun _f hnf hsf =>
  Not.elim hnf.ne <| empty_mem_iff_bot.1 <| le_principal_iff.1 hsf
#align is_compact_empty isCompact_empty

@[simp]
theorem isCompact_singleton {a : α} : IsCompact ({a} : Set α) := fun f hf hfa =>
  ⟨a, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds a) hf⟩
#align is_compact_singleton isCompact_singleton

theorem Set.Subsingleton.isCompact {s : Set α} (hs : s.Subsingleton) : IsCompact s :=
  Subsingleton.induction_on hs isCompact_empty fun _ => isCompact_singleton
#align set.subsingleton.is_compact Set.Subsingleton.isCompact

-- porting note: golfed a proof instead of fixing it
theorem Set.Finite.isCompact_biUnion {s : Set ι} {f : ι → Set α} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCompact (f i)) : IsCompact (⋃ i ∈ s, f i) :=
  isCompact_iff_ultrafilter_le_nhds'.2 <| fun l hl => by
    rw [Ultrafilter.finite_biUnion_mem_iff hs] at hl
    rcases hl with ⟨i, his, hi⟩
    rcases (hf i his).ultrafilter_le_nhds _ (le_principal_iff.2 hi) with ⟨x, hxi, hlx⟩
    exact ⟨x, mem_iUnion₂.2 ⟨i, his, hxi⟩, hlx⟩
#align set.finite.is_compact_bUnion Set.Finite.isCompact_biUnion

theorem Finset.isCompact_biUnion (s : Finset ι) {f : ι → Set α} (hf : ∀ i ∈ s, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  s.finite_toSet.isCompact_biUnion hf
#align finset.is_compact_bUnion Finset.isCompact_biUnion

theorem isCompact_accumulate {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (n : ℕ) :
    IsCompact (Accumulate K n) :=
  (finite_le_nat n).isCompact_biUnion fun k _ => hK k
#align is_compact_accumulate isCompact_accumulate

-- porting note: new lemma
theorem Set.Finite.isCompact_sUnion {S : Set (Set α)} (hf : S.Finite) (hc : ∀ s ∈ S, IsCompact s) :
    IsCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCompact_biUnion hc

-- porting note: generalized to `ι : Sort*`
theorem isCompact_iUnion {ι : Sort*} {f : ι → Set α} [Finite ι] (h : ∀ i, IsCompact (f i)) :
    IsCompact (⋃ i, f i) :=
  (finite_range f).isCompact_sUnion <| forall_range_iff.2 h
#align is_compact_Union isCompact_iUnion

theorem Set.Finite.isCompact (hs : s.Finite) : IsCompact s :=
  biUnion_of_singleton s ▸ hs.isCompact_biUnion fun _ _ => isCompact_singleton
#align set.finite.is_compact Set.Finite.isCompact

theorem IsCompact.finite_of_discrete [DiscreteTopology α] {s : Set α} (hs : IsCompact s) :
    s.Finite := by
  have : ∀ x : α, ({x} : Set α) ∈ 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, _, hst⟩
  simp only [← t.set_biUnion_coe, biUnion_of_singleton] at hst
  exact t.finite_toSet.subset hst
#align is_compact.finite_of_discrete IsCompact.finite_of_discrete

theorem isCompact_iff_finite [DiscreteTopology α] {s : Set α} : IsCompact s ↔ s.Finite :=
  ⟨fun h => h.finite_of_discrete, fun h => h.isCompact⟩
#align is_compact_iff_finite isCompact_iff_finite

theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  rw [union_eq_iUnion]; exact isCompact_iUnion fun b => by cases b <;> assumption
#align is_compact.union IsCompact.union

protected theorem IsCompact.insert (hs : IsCompact s) (a) : IsCompact (insert a s) :=
  isCompact_singleton.union hs
#align is_compact.insert IsCompact.insert

-- porting note: todo: reformulate using `𝓝ˢ`
/-- If `V : ι → Set α` is a decreasing family of closed compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed because `α` is
not assumed to be Hausdorff. See `exists_subset_nhd_of_compact` for version assuming this. -/
theorem exists_subset_nhds_of_isCompact' {ι : Type*} [Nonempty ι] {V : ι → Set α}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) (hV_closed : ∀ i, IsClosed (V i))
    {U : Set α} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U := by
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU
  suffices : ∃ i, V i ⊆ W
  · exact this.imp fun i hi => hi.trans hWU
  by_contra' H
  replace H : ∀ i, (V i ∩ Wᶜ).Nonempty := fun i => Set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i ∩ Wᶜ).Nonempty := by
    refine'
      IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed _ (fun i j => _) H
        (fun i => (hV_cpct i).inter_right W_op.isClosed_compl) fun i =>
        (hV_closed i).inter W_op.isClosed_compl
    rcases hV i j with ⟨k, hki, hkj⟩
    refine' ⟨k, ⟨fun x => _, fun x => _⟩⟩ <;> simp only [and_imp, mem_inter_iff, mem_compl_iff] <;>
      tauto
  have : ¬⋂ i : ι, V i ⊆ W := by simpa [← iInter_inter, inter_compl_nonempty_iff]
  contradiction
#align exists_subset_nhds_of_is_compact' exists_subset_nhds_of_isCompact'

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
theorem isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι → Set α)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨β, f, e, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
    refine' ⟨t.image f', Set.Finite.intro inferInstance, le_antisymm _ _⟩
    · refine' Set.Subset.trans ht _
      simp only [Set.iUnion_subset_iff]
      intro i hi
      erw [← Set.iUnion_subtype (fun x : ι => x ∈ t.image f') fun i => b i.1]
      exact Set.subset_iUnion (fun i : t.image f' => b i) ⟨_, Finset.mem_image_of_mem _ hi⟩
    · apply Set.iUnion₂_subset
      rintro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      rw [e]
      exact Set.subset_iUnion (b ∘ f') j
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)
#align is_compact_open_iff_eq_finite_Union_of_is_topological_basis isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis

namespace Filter

/-- `Filter.cocompact` is the filter generated by complements to compact sets. -/
def cocompact (α : Type*) [TopologicalSpace α] : Filter α :=
  ⨅ (s : Set α) (_ : IsCompact s), 𝓟 sᶜ
#align filter.cocompact Filter.cocompact

theorem hasBasis_cocompact : (cocompact α).HasBasis IsCompact compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 (subset_union_left s t),
        compl_subset_compl.2 (subset_union_right s t)⟩)
    ⟨∅, isCompact_empty⟩
#align filter.has_basis_cocompact Filter.hasBasis_cocompact

theorem mem_cocompact : s ∈ cocompact α ↔ ∃ t, IsCompact t ∧ tᶜ ⊆ s :=
  hasBasis_cocompact.mem_iff
#align filter.mem_cocompact Filter.mem_cocompact

theorem mem_cocompact' : s ∈ cocompact α ↔ ∃ t, IsCompact t ∧ sᶜ ⊆ t :=
  mem_cocompact.trans <| exists_congr fun _ => and_congr_right fun _ => compl_subset_comm
#align filter.mem_cocompact' Filter.mem_cocompact'

theorem _root_.IsCompact.compl_mem_cocompact (hs : IsCompact s) : sᶜ ∈ Filter.cocompact α :=
  hasBasis_cocompact.mem_of_mem hs
#align is_compact.compl_mem_cocompact IsCompact.compl_mem_cocompact

theorem cocompact_le_cofinite : cocompact α ≤ cofinite := fun s hs =>
  compl_compl s ▸ hs.isCompact.compl_mem_cocompact
#align filter.cocompact_le_cofinite Filter.cocompact_le_cofinite

theorem cocompact_eq_cofinite (α : Type*) [TopologicalSpace α] [DiscreteTopology α] :
    cocompact α = cofinite := by
  simp only [cocompact, hasBasis_cofinite.eq_biInf, isCompact_iff_finite]
#align filter.cocompact_eq_cofinite Filter.cocompact_eq_cofinite

@[simp] theorem _root_.Nat.cocompact_eq : cocompact ℕ = atTop :=
  (cocompact_eq_cofinite ℕ).trans Nat.cofinite_eq_atTop
#align nat.cocompact_eq Nat.cocompact_eq

theorem Tendsto.isCompact_insert_range_of_cocompact {f : α → β} {b}
    (hf : Tendsto f (cocompact α) (𝓝 b)) (hfc : Continuous f) : IsCompact (insert b (range f)) := by
  intro l hne hle
  by_cases hb : ClusterPt b l
  · exact ⟨b, Or.inl rfl, hb⟩
  simp only [clusterPt_iff, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hb
  rcases hb with ⟨s, hsb, t, htl, hd⟩
  rcases mem_cocompact.1 (hf hsb) with ⟨K, hKc, hKs⟩
  have : f '' K ∈ l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsb, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
  exact ⟨y, Or.inr <| image_subset_range _ _ hy, hyl⟩
#align filter.tendsto.is_compact_insert_range_of_cocompact Filter.Tendsto.isCompact_insert_range_of_cocompact

theorem Tendsto.isCompact_insert_range_of_cofinite {f : ι → α} {a} (hf : Tendsto f cofinite (𝓝 a)) :
    IsCompact (insert a (range f)) := by
  letI : TopologicalSpace ι := ⊥; haveI h : DiscreteTopology ι := ⟨rfl⟩
  rw [← cocompact_eq_cofinite ι] at hf
  exact hf.isCompact_insert_range_of_cocompact continuous_of_discreteTopology
#align filter.tendsto.is_compact_insert_range_of_cofinite Filter.Tendsto.isCompact_insert_range_of_cofinite

theorem Tendsto.isCompact_insert_range {f : ℕ → α} {a} (hf : Tendsto f atTop (𝓝 a)) :
    IsCompact (insert a (range f)) :=
  Filter.Tendsto.isCompact_insert_range_of_cofinite <| Nat.cofinite_eq_atTop.symm ▸ hf
#align filter.tendsto.is_compact_insert_range Filter.Tendsto.isCompact_insert_range

/-- `Filter.coclosedCompact` is the filter generated by complements to closed compact sets.
In a Hausdorff space, this is the same as `Filter.cocompact`. -/
def coclosedCompact (α : Type*) [TopologicalSpace α] : Filter α :=
  ⨅ (s : Set α) (_ : IsClosed s) (_ : IsCompact s), 𝓟 sᶜ
#align filter.coclosed_compact Filter.coclosedCompact

theorem hasBasis_coclosedCompact :
    (Filter.coclosedCompact α).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, iInf_and']
  refine' hasBasis_biInf_principal' _ ⟨∅, isClosed_empty, isCompact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 (subset_union_left _ _),
    compl_subset_compl.2 (subset_union_right _ _)⟩⟩
#align filter.has_basis_coclosed_compact Filter.hasBasis_coclosedCompact

theorem mem_coclosedCompact : s ∈ coclosedCompact α ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ tᶜ ⊆ s := by
  simp only [hasBasis_coclosedCompact.mem_iff, and_assoc]
#align filter.mem_coclosed_compact Filter.mem_coclosedCompact

theorem mem_coclosed_compact' : s ∈ coclosedCompact α ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ sᶜ ⊆ t := by
  simp only [mem_coclosedCompact, compl_subset_comm]
#align filter.mem_coclosed_compact' Filter.mem_coclosed_compact'

theorem cocompact_le_coclosedCompact : cocompact α ≤ coclosedCompact α :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl
#align filter.cocompact_le_coclosed_compact Filter.cocompact_le_coclosedCompact

end Filter

theorem IsCompact.compl_mem_coclosedCompact_of_isClosed (hs : IsCompact s) (hs' : IsClosed s) :
    sᶜ ∈ Filter.coclosedCompact α :=
  hasBasis_coclosedCompact.mem_of_mem ⟨hs', hs⟩
#align is_compact.compl_mem_coclosed_compact_of_is_closed IsCompact.compl_mem_coclosedCompact_of_isClosed

namespace Bornology

variable (α)

/-- Sets that are contained in a compact set form a bornology. Its `cobounded` filter is
`Filter.cocompact`. See also `Bornology.relativelyCompact` the bornology of sets with compact
closure. -/
def inCompact : Bornology α where
  cobounded' := Filter.cocompact α
  le_cofinite' := Filter.cocompact_le_cofinite
#align bornology.in_compact Bornology.inCompact

variable {α}

theorem inCompact.isBounded_iff : @IsBounded _ (inCompact α) s ↔ ∃ t, IsCompact t ∧ s ⊆ t := by
  change sᶜ ∈ Filter.cocompact α ↔ _
  rw [Filter.mem_cocompact]
  simp
#align bornology.in_compact.is_bounded_iff Bornology.inCompact.isBounded_iff

end Bornology

#noalign nhds_contain_boxes
#noalign nhds_contain_boxes.symm
#noalign nhds_contain_boxes.comm
#noalign nhds_contain_boxes_of_singleton
#noalign nhds_contain_boxes_of_compact

/-- If `s` and `t` are compact sets, then the set neighborhoods filter of `s ×ˢ t`
is the product of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_prod_le`. -/
theorem IsCompact.nhdsSet_prod_eq {s : Set α} {t : Set β} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  simp_rw [hs.nhdsSet_prod_eq_biSup, ht.prod_nhdsSet_eq_biSup, nhdsSet, sSup_image, biSup_prod,
    nhds_prod_eq]

/-- The product of a neighborhood of `s` and a neighborhood of `t` is a neighborhood of `s ×ˢ t`,
formulated in terms of a filter inequality. -/
theorem nhdsSet_prod_le (s : Set α) (t : Set β) : 𝓝ˢ (s ×ˢ t) ≤ 𝓝ˢ s ×ˢ 𝓝ˢ t :=
  ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ ↦
    (huo.prod hvo).mem_nhdsSet.2 <| prod_mono hsu htv

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`.

See also `IsCompact.nhdsSet_prod_eq`. -/
theorem generalized_tube_lemma {s : Set α} (hs : IsCompact s) {t : Set β} (ht : IsCompact t)
    {n : Set (α × β)} (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set α) (v : Set β), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by
  rw [← hn.mem_nhdsSet, hs.nhdsSet_prod_eq ht,
    ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).mem_iff] at hp
  rcases hp with ⟨⟨u, v⟩, ⟨⟨huo, hsu⟩, hvo, htv⟩, hn⟩
  exact ⟨u, v, huo, hvo, hsu, htv, hn⟩
#align generalized_tube_lemma generalized_tube_lemma

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class CompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (univ : Set α)
#align compact_space CompactSpace

-- see Note [lower instance priority]
instance (priority := 10) Subsingleton.compactSpace [Subsingleton α] : CompactSpace α :=
  ⟨subsingleton_univ.isCompact⟩
#align subsingleton.compact_space Subsingleton.compactSpace

theorem isCompact_univ_iff : IsCompact (univ : Set α) ↔ CompactSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
#align is_compact_univ_iff isCompact_univ_iff

theorem isCompact_univ [h : CompactSpace α] : IsCompact (univ : Set α) :=
  h.isCompact_univ
#align is_compact_univ isCompact_univ

theorem cluster_point_of_compact [CompactSpace α] (f : Filter α) [NeBot f] : ∃ x, ClusterPt x f :=
  by simpa using isCompact_univ (show f ≤ 𝓟 univ by simp)
#align cluster_point_of_compact cluster_point_of_compact

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace α] (F : Ultrafilter α) : ↑F ≤ 𝓝 F.lim := by
  rcases isCompact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩
  exact le_nhds_lim ⟨x, h⟩
set_option linter.uppercaseLean3 false in
#align ultrafilter.le_nhds_Lim Ultrafilter.le_nhds_lim

theorem CompactSpace.elim_nhds_subcover [CompactSpace α] (U : α → Set α) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, ⋃ x ∈ t, U x = ⊤ := by
  obtain ⟨t, -, s⟩ := IsCompact.elim_nhds_subcover isCompact_univ U fun x _ => hU x
  exact ⟨t, top_unique s⟩
#align compact_space.elim_nhds_subcover CompactSpace.elim_nhds_subcover

theorem compactSpace_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} (Z : ι → Set α), (∀ i, IsClosed (Z i)) → ⋂ i, Z i = ∅ →
      ∃ t : Finset ι, ⋂ i ∈ t, Z i = ∅) :
    CompactSpace α where
  isCompact_univ := isCompact_of_finite_subfamily_closed fun Z => by
    simpa using h Z
#align compact_space_of_finite_subfamily_closed compactSpace_of_finite_subfamily_closed

theorem IsClosed.isCompact [CompactSpace α] {s : Set α} (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)
#align is_closed.is_compact IsClosed.isCompact

/-- If a filter has a unique cluster point `y` in a compact topological space,
then the filter is less than or equal to `𝓝 y`. -/
lemma le_nhds_of_unique_clusterPt [CompactSpace α] {l : Filter α} {y : α}
    (h : ∀ x, ClusterPt x l → x = y) : l ≤ 𝓝 y :=
  isCompact_univ.le_nhds_of_unique_clusterPt univ_mem fun x _ ↦ h x

/-- If `y` is a unique `MapClusterPt` for `f` along `l`
and the codomain of `f` is a compact space,
then `f` tends to `𝓝 y` along `l`. -/
lemma tendsto_nhds_of_unique_mapClusterPt [CompactSpace α] {l : Filter β} {y : α} {f : β → α}
    (h : ∀ x, MapClusterPt x l f → x = y) :
    Tendsto f l (𝓝 y) :=
  le_nhds_of_unique_clusterPt h

/-- `α` is a noncompact topological space if it is not a compact space. -/
class NoncompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a noncompact space, `Set.univ` is not a compact set. -/
  noncompact_univ : ¬IsCompact (univ : Set α)
#align noncompact_space NoncompactSpace

-- porting note: a lemma instead of `export` to make `α` explicit
lemma noncompact_univ (α : Type*) [TopologicalSpace α] [NoncompactSpace α] :
    ¬IsCompact (univ : Set α) :=
  NoncompactSpace.noncompact_univ

theorem IsCompact.ne_univ [NoncompactSpace α] {s : Set α} (hs : IsCompact s) : s ≠ univ := fun h =>
  noncompact_univ α (h ▸ hs)
#align is_compact.ne_univ IsCompact.ne_univ

instance [NoncompactSpace α] : NeBot (Filter.cocompact α) := by
  refine' Filter.hasBasis_cocompact.neBot_iff.2 fun hs => _
  contrapose hs; rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]; exact noncompact_univ α

@[simp]
theorem Filter.cocompact_eq_bot [CompactSpace α] : Filter.cocompact α = ⊥ :=
  Filter.hasBasis_cocompact.eq_bot_iff.mpr ⟨Set.univ, isCompact_univ, Set.compl_univ⟩
#align filter.cocompact_eq_bot Filter.cocompact_eq_bot

instance [NoncompactSpace α] : NeBot (Filter.coclosedCompact α) :=
  neBot_of_le Filter.cocompact_le_coclosedCompact

theorem noncompactSpace_of_neBot (_ : NeBot (Filter.cocompact α)) : NoncompactSpace α :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩
#align noncompact_space_of_ne_bot noncompactSpace_of_neBot

theorem Filter.cocompact_neBot_iff : NeBot (Filter.cocompact α) ↔ NoncompactSpace α :=
  ⟨noncompactSpace_of_neBot, fun _ => inferInstance⟩
#align filter.cocompact_ne_bot_iff Filter.cocompact_neBot_iff

theorem not_compactSpace_iff : ¬CompactSpace α ↔ NoncompactSpace α :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩
#align not_compact_space_iff not_compactSpace_iff

instance : NoncompactSpace ℤ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

-- Note: We can't make this into an instance because it loops with `Finite.compactSpace`.
/-- A compact discrete space is finite. -/
theorem finite_of_compact_of_discrete [CompactSpace α] [DiscreteTopology α] : Finite α :=
  Finite.of_finite_univ <| isCompact_univ.finite_of_discrete
#align finite_of_compact_of_discrete finite_of_compact_of_discrete

theorem exists_nhds_ne_neBot (α : Type*) [TopologicalSpace α] [CompactSpace α] [Infinite α] :
    ∃ z : α, (𝓝[≠] z).NeBot := by
  by_contra' H
  simp_rw [not_neBot] at H
  haveI := discreteTopology_iff_nhds_ne.2 H
  exact Infinite.not_finite (finite_of_compact_of_discrete : Finite α)
#align exists_nhds_ne_ne_bot exists_nhds_ne_neBot

theorem finite_cover_nhds_interior [CompactSpace α] {U : α → Set α} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, ⋃ x ∈ t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩
#align finite_cover_nhds_interior finite_cover_nhds_interior

theorem finite_cover_nhds [CompactSpace α] {U : α → Set α} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, ⋃ x ∈ t, U x = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
  ⟨t, univ_subset_iff.1 <| ht.symm.subset.trans <| iUnion₂_mono fun _ _ => interior_subset⟩
#align finite_cover_nhds finite_cover_nhds

/-- If `α` is a compact space, then a locally finite family of sets of `α` can have only finitely
many nonempty elements. -/
theorem LocallyFinite.finite_nonempty_of_compact {ι : Type*} [CompactSpace α] {f : ι → Set α}
    (hf : LocallyFinite f) : { i | (f i).Nonempty }.Finite := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ
#align locally_finite.finite_nonempty_of_compact LocallyFinite.finite_nonempty_of_compact

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `Set.Finite` version. -/
theorem LocallyFinite.finite_of_compact {ι : Type*} [CompactSpace α] {f : ι → Set α}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Finite := by
  simpa only [hne] using hf.finite_nonempty_of_compact
#align locally_finite.finite_of_compact LocallyFinite.finite_of_compact

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `Fintype` version. -/
noncomputable def LocallyFinite.fintypeOfCompact {ι : Type*} [CompactSpace α] {f : ι → Set α}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)
#align locally_finite.fintype_of_compact LocallyFinite.fintypeOfCompact

/-- The comap of the cocompact filter on `β` by a continuous function `f : α → β` is less than or
equal to the cocompact filter on `α`.
This is a reformulation of the fact that images of compact sets are compact. -/
theorem Filter.comap_cocompact_le {f : α → β} (hf : Continuous f) :
    (Filter.cocompact β).comap f ≤ Filter.cocompact α := by
  rw [(Filter.hasBasis_cocompact.comap f).le_basis_iff Filter.hasBasis_cocompact]
  intro t ht
  refine' ⟨f '' t, ht.image hf, _⟩
  simpa using t.subset_preimage_image f
#align filter.comap_cocompact_le Filter.comap_cocompact_le

theorem isCompact_range [CompactSpace α] {f : α → β} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf
#align is_compact_range isCompact_range

theorem isCompact_diagonal [CompactSpace α] : IsCompact (diagonal α) :=
  @range_diag α ▸ isCompact_range (continuous_id.prod_mk continuous_id)
#align is_compact_diagonal isCompact_diagonal

-- porting note: renamed, golfed
/-- If `X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map. -/
theorem isClosedMap_snd_of_compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {Y : Type*} [TopologicalSpace Y] : IsClosedMap (Prod.snd : X × Y → Y) := fun s hs => by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  have : univ ×ˢ {y} ⊆ sᶜ
  · exact fun (x, y') ⟨_, rfl⟩ hs => hy ⟨(x, y'), hs, rfl⟩
  rcases generalized_tube_lemma isCompact_univ isCompact_singleton hs.isOpen_compl this
    with ⟨U, V, -, hVo, hU, hV, hs⟩
  refine mem_nhds_iff.2 ⟨V, ?_, hVo, hV rfl⟩
  rintro _ hzV ⟨z, hzs, rfl⟩
  exact hs ⟨hU trivial, hzV⟩ hzs
#align is_closed_proj_of_is_compact isClosedMap_snd_of_compactSpace

/-- If `Y` is a compact topological space, then `Prod.fst : X × Y → X` is a closed map. -/
theorem isClosedMap_fst_of_compactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] : IsClosedMap (Prod.fst : X × Y → X) :=
  isClosedMap_snd_of_compactSpace.comp isClosedMap_swap

theorem exists_subset_nhds_of_compactSpace [CompactSpace α] {ι : Type*} [Nonempty ι]
    {V : ι → Set α} (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set α}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU
#align exists_subset_nhds_of_compact_space exists_subset_nhds_of_compactSpace

/-- If `f : α → β` is an `Inducing` map, the image `f '' s` of a set `s` is compact
  if and only if `s` is compact. -/
theorem Inducing.isCompact_iff {f : α → β} (hf : Inducing f) {s : Set α} :
    IsCompact s ↔ IsCompact (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩
#align inducing.is_compact_iff Inducing.isCompact_iff

/-- If `f : α → β` is an `Embedding`, the image `f '' s` of a set `s` is compact
  if and only if `s` is compact. -/
theorem Embedding.isCompact_iff {f : α → β} (hf : Embedding f) :
    IsCompact s ↔ IsCompact (f '' s) := hf.toInducing.isCompact_iff
#align embedding.is_compact_iff_is_compact_image Embedding.isCompact_iff

/-- The preimage of a compact set under an inducing map is a compact set. -/
theorem Inducing.isCompact_preimage {f : α → β} (hf : Inducing f) (hf' : IsClosed (range f))
    {K : Set β} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isCompact_iff, image_preimage_eq_inter_range]

/-- The preimage of a compact set under a closed embedding is a compact set. -/
theorem ClosedEmbedding.isCompact_preimage {f : α → β} (hf : ClosedEmbedding f)
    {K : Set β} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.toInducing.isCompact_preimage (hf.closed_range) hK
#align closed_embedding.is_compact_preimage ClosedEmbedding.isCompact_preimage

/-- A closed embedding is proper, ie, inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `ClosedEmbedding.isCompact_preimage`. -/
theorem ClosedEmbedding.tendsto_cocompact {f : α → β} (hf : ClosedEmbedding f) :
    Tendsto f (Filter.cocompact α) (Filter.cocompact β) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact
#align closed_embedding.tendsto_cocompact ClosedEmbedding.tendsto_cocompact

/-- Sets of subtype are compact iff the image under a coercion is. -/
theorem Subtype.isCompact_iff {p : α → Prop} {s : Set { a // p a }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set α) :=
  embedding_subtype_val.isCompact_iff
#align is_compact_iff_is_compact_in_subtype Subtype.isCompact_iff

theorem isCompact_iff_isCompact_univ {s : Set α} : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]
#align is_compact_iff_is_compact_univ isCompact_iff_isCompact_univ

theorem isCompact_iff_compactSpace {s : Set α} : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff
#align is_compact_iff_compact_space isCompact_iff_compactSpace

theorem IsCompact.finite {s : Set α} (hs : IsCompact s) (hs' : DiscreteTopology s) : s.Finite :=
  finite_coe_iff.mp (@finite_of_compact_of_discrete _ _ (isCompact_iff_compactSpace.mp hs) hs')
#align is_compact.finite IsCompact.finite

theorem exists_nhds_ne_inf_principal_neBot {s : Set α} (hs : IsCompact s) (hs' : s.Infinite) :
    ∃ z ∈ s, (𝓝[≠] z ⊓ 𝓟 s).NeBot := by
  by_contra' H
  simp_rw [not_neBot] at H
  exact hs' (hs.finite <| discreteTopology_subtype_iff.mpr H)
#align exists_nhds_ne_inf_principal_ne_bot exists_nhds_ne_inf_principal_neBot

protected theorem ClosedEmbedding.noncompactSpace [NoncompactSpace α] {f : α → β}
    (hf : ClosedEmbedding f) : NoncompactSpace β :=
  noncompactSpace_of_neBot hf.tendsto_cocompact.neBot
#align closed_embedding.noncompact_space ClosedEmbedding.noncompactSpace

protected theorem ClosedEmbedding.compactSpace [h : CompactSpace β] {f : α → β}
    (hf : ClosedEmbedding f) : CompactSpace α :=
  ⟨by rw [hf.toInducing.isCompact_iff, image_univ]; exact hf.closed_range.isCompact⟩
#align closed_embedding.compact_space ClosedEmbedding.compactSpace

theorem IsCompact.prod {s : Set α} {t : Set β} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨a : α, sa : a ∈ s, ha : map Prod.fst f.1 ≤ 𝓝 a⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨b : β, tb : b ∈ t, hb : map Prod.snd f.1 ≤ 𝓝 b⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at ha hb
  refine' ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩
  rw [nhds_prod_eq]; exact le_inf ha hb
#align is_compact.prod IsCompact.prod

/-- Finite topological spaces are compact. -/
instance (priority := 100) Finite.compactSpace [Finite α] : CompactSpace α where
  isCompact_univ := finite_univ.isCompact
#align finite.compact_space Finite.compactSpace

/-- The product of two compact spaces is compact. -/
instance [CompactSpace α] [CompactSpace β] : CompactSpace (α × β) :=
  ⟨by rw [← univ_prod_univ]; exact isCompact_univ.prod isCompact_univ⟩

/-- The disjoint union of two compact spaces is compact. -/
instance [CompactSpace α] [CompactSpace β] : CompactSpace (α ⊕ β) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)⟩

instance [Finite ι] [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] :
    CompactSpace (Σi, π i) := by
  refine' ⟨_⟩
  rw [Sigma.univ]
  exact isCompact_iUnion fun i => isCompact_range continuous_sigmaMk

/-- The coproduct of the cocompact filters on two topological spaces is the cocompact filter on
their product. -/
theorem Filter.coprod_cocompact :
    (Filter.cocompact α).coprod (Filter.cocompact β) = Filter.cocompact (α × β) := by
  apply le_antisymm
  · exact sup_le (comap_cocompact_le continuous_fst) (comap_cocompact_le continuous_snd)
  · refine (hasBasis_cocompact.coprod hasBasis_cocompact).ge_iff.2 fun K hK ↦ ?_
    rw [← univ_prod, ← prod_univ, ← compl_prod_eq_union]
    exact (hK.1.prod hK.2).compl_mem_cocompact
#align filter.coprod_cocompact Filter.coprod_cocompact

theorem Prod.noncompactSpace_iff :
    NoncompactSpace (α × β) ↔ NoncompactSpace α ∧ Nonempty β ∨ Nonempty α ∧ NoncompactSpace β := by
  simp [← Filter.cocompact_neBot_iff, ← Filter.coprod_cocompact, Filter.coprod_neBot_iff]
#align prod.noncompact_space_iff Prod.noncompactSpace_iff

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_left [NoncompactSpace α] [Nonempty β] :
    NoncompactSpace (α × β) :=
  Prod.noncompactSpace_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)
#align prod.noncompact_space_left Prod.noncompactSpace_left

-- See Note [lower instance priority]
instance (priority := 100) Prod.noncompactSpace_right [Nonempty α] [NoncompactSpace β] :
    NoncompactSpace (α × β) :=
  Prod.noncompactSpace_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)
#align prod.noncompact_space_right Prod.noncompactSpace_right

section Tychonoff

variable [∀ i, TopologicalSpace (π i)]

/-- **Tychonoff's theorem**: product of compact sets is compact. -/
theorem isCompact_pi_infinite {s : ∀ i, Set (π i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
  simp only [isCompact_iff_ultrafilter_le_nhds, nhds_pi, Filter.pi, exists_prop, mem_setOf_eq,
    le_iInf_iff, le_principal_iff]
  intro h f hfs
  have : ∀ i : ι, ∃ a, a ∈ s i ∧ Tendsto (Function.eval i) f (𝓝 a) := by
    refine fun i => h i (f.map _) (mem_map.2 ?_)
    exact mem_of_superset hfs fun x hx => hx i
  choose a ha using this
  exact ⟨a, fun i => (ha i).left, fun i => (ha i).right.le_comap⟩
#align is_compact_pi_infinite isCompact_pi_infinite

/-- **Tychonoff's theorem** formulated using `Set.pi`: product of compact sets is compact. -/
theorem isCompact_univ_pi {s : ∀ i, Set (π i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact (pi univ s) := by
  convert isCompact_pi_infinite h
  simp only [← mem_univ_pi, setOf_mem_eq]
#align is_compact_univ_pi isCompact_univ_pi

instance Pi.compactSpace [∀ i, CompactSpace (π i)] : CompactSpace (∀ i, π i) :=
  ⟨by rw [← pi_univ univ]; exact isCompact_univ_pi fun i => isCompact_univ⟩
#align pi.compact_space Pi.compactSpace

instance Function.compactSpace [CompactSpace β] : CompactSpace (ι → β) :=
  Pi.compactSpace
#align function.compact_space Function.compactSpace

/-- **Tychonoff's theorem** formulated in terms of filters: `Filter.cocompact` on an indexed product
type `Π d, κ d` the `Filter.coprodᵢ` of filters `Filter.cocompact` on `κ d`. -/
theorem Filter.coprodᵢ_cocompact {δ : Type*} {κ : δ → Type*} [∀ d, TopologicalSpace (κ d)] :
    (Filter.coprodᵢ fun d => Filter.cocompact (κ d)) = Filter.cocompact (∀ d, κ d) := by
  refine' le_antisymm (iSup_le fun i => Filter.comap_cocompact_le (continuous_apply i)) _
  refine' compl_surjective.forall.2 fun s H => _
  simp only [compl_mem_coprodᵢ, Filter.mem_cocompact, compl_subset_compl, image_subset_iff] at H ⊢
  choose K hKc htK using H
  exact ⟨Set.pi univ K, isCompact_univ_pi hKc, fun f hf i _ => htK i hf⟩
set_option linter.uppercaseLean3 false in
#align filter.Coprod_cocompact Filter.coprodᵢ_cocompact

end Tychonoff

instance Quot.compactSpace {r : α → α → Prop} [CompactSpace α] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact isCompact_range continuous_quot_mk⟩
#align quot.compact_space Quot.compactSpace

instance Quotient.compactSpace {s : Setoid α} [CompactSpace α] : CompactSpace (Quotient s) :=
  Quot.compactSpace
#align quotient.compact_space Quotient.compactSpace

theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace α] {S : Set α}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ V : Set α, V ⊆ S ∧ V.Nonempty ∧ IsClosed V ∧
      ∀ V' : Set α, V' ⊆ V → V'.Nonempty → IsClosed V' → V' = V := by
  let opens := { U : Set α | Sᶜ ⊆ U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, ⟨Uc, Uo, Ucne⟩, h⟩ :=
    zorn_subset opens fun c hc hz => by
      by_cases hcne : c.Nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        haveI : Nonempty { U // U ∈ c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, -, -⟩ := hc hU₀
        use ⋃₀ c
        refine' ⟨⟨_, _, _⟩, fun U hU a ha => ⟨U, hU, ha⟩⟩
        · exact fun a ha => ⟨U₀, hU₀, U₀compl ha⟩
        · exact isOpen_sUnion fun _ h => (hc h).2.1
        · convert_to (⋂ U : { U // U ∈ c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, exists_prop, not_and, Set.mem_iInter, Subtype.forall,
              mem_setOf_eq, mem_compl_iff, mem_sUnion]
          apply IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := hz.directedOn U hU U' hU'
            exact ⟨⟨V, hVc⟩, Set.compl_subset_compl.mpr hVU, Set.compl_subset_compl.mpr hVU'⟩
          · exact fun U => (hc U.2).2.2
          · exact fun U => (hc U.2).2.1.isClosed_compl.isCompact
          · exact fun U => (hc U.2).2.1.isClosed_compl
      · use Sᶜ
        refine' ⟨⟨Set.Subset.refl _, isOpen_compl_iff.mpr hS, _⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
  refine' ⟨Uᶜ, Set.compl_subset_comm.mp Uc, Ucne, Uo.isClosed_compl, _⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine' h V'ᶜ ⟨_, isOpen_compl_iff.mpr V'cls, _⟩ (Set.subset_compl_comm.mp V'sub)
    exact Set.Subset.trans Uc (Set.subset_compl_comm.mp V'sub)
    simp only [compl_compl, V'ne]
  rw [← this, compl_compl]
#align is_closed.exists_minimal_nonempty_closed_subset IsClosed.exists_minimal_nonempty_closed_subset
