/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Order.Filter.Pi
import Mathlib.Topology.Bases
import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Accumulate
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Order.Minimal

#align_import topology.subset_properties from "leanprover-community/mathlib"@"3efd324a3a31eaa40c9d5bfc669c4fafee5f9423"

/-!
# Properties of subsets of topological spaces

In this file we define various properties of subsets of a topological space, and some classes on
topological spaces.

## Main definitions

We define the following properties for sets in a topological space:

* `IsCompact`: each open cover has a finite subcover. This is defined in mathlib using filters.
  The main property of a compact set is `IsCompact.elim_finite_subcover`.
* `IsClopen`: a set that is both open and closed.
* `IsIrreducible`: a nonempty set that has contains no non-trivial pair of disjoint opens.
  See also the section below in the module doc.

For each of these definitions (except for `IsClopen`), we also have a class stating that the whole
space satisfies that property:
`CompactSpace`, `IrreducibleSpace`

Furthermore, we have three more classes:
* `LocallyCompactSpace`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
* `SigmaCompactSpace`: a space that is the union of a countably many compact subspaces;
* `NoncompactSpace`: a space that is not a compact space.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
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
theorem isCompact_of_isClosed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht
#align is_compact_of_is_closed_subset isCompact_of_isClosed_subset

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
    (iUnion_eq_iUnion_finset U ▸ hsU) (directed_of_sup fun _ _ h => biUnion_subset_biUnion_left h)
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
  refine'
    (hasBasis_nhdsSet _).disjoint_iff_left.2
      ⟨⋃ x ∈ t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, _⟩
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
    (by rwa [← iInter_eq_iInter_finset]) (directed_of_sup fun _ _ h ↦ biInter_subset_biInter_left h)
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
  simp only [nonempty_iff_ne_empty] at hsZ ⊢
  apply mt (hs.elim_finite_subfamily_closed Z hZc); push_neg; exact hsZ
#align is_compact.inter_Inter_nonempty IsCompact.inter_iInter_nonempty

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed {ι : Type v} [hι : Nonempty ι]
    (Z : ι → Set α) (hZd : Directed (· ⊇ ·) Z) (hZn : ∀ i, (Z i).Nonempty)
    (hZc : ∀ i, IsCompact (Z i)) (hZcl : ∀ i, IsClosed (Z i)) : (⋂ i, Z i).Nonempty := by
  let i₀ := hι.some
  suffices (Z i₀ ∩ ⋂ i, Z i).Nonempty by
    rwa [inter_eq_right_iff_subset.mpr (iInter_subset _ i₀)] at this
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
  have hZd : Directed (· ⊇ ·) Z := directed_of_sup Zmono
  have : ∀ i, Z i ⊆ Z 0 := fun i => Zmono <| zero_le i
  have hZc : ∀ i, IsCompact (Z i) := fun i => isCompact_of_isClosed_subset hZ0 (hZcl i) (this i)
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

/-- To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : α} {K : Set β} (hK : IsCompact K)
    {P : α → β → Prop} (hP : ∀ y ∈ K, ∀ᶠ z : α × β in 𝓝 (x₀, y), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y := by
  refine' hK.induction_on _ _ _ _
  · exact eventually_of_forall fun x y => False.elim
  · intro s t hst ht
    refine' ht.mono fun x h y hys => h y <| hst hys
  · intro s t hs ht
    filter_upwards [hs, ht]
    rintro x h1 h2 y (hys | hyt)
    exacts [h1 y hys, h2 y hyt]
  · intro y hyK
    specialize hP y hyK
    rw [nhds_prod_eq, eventually_prod_iff] at hP
    rcases hP with ⟨p, hp, q, hq, hpq⟩
    exact ⟨{ y | q y }, mem_nhdsWithin_of_mem_nhds hq, eventually_of_mem hp @hpq⟩
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
  isCompact_iff_ultrafilter_le_nhds.2 <| fun l hl => by
    rw [le_principal_iff, Ultrafilter.mem_coe, Ultrafilter.finite_biUnion_mem_iff hs] at hl
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
    filter_upwards [htl, le_principal_iff.1 hle]with y hyt hyf
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

section TubeLemma

/-- `NhdsContainBoxes s t` means that any open neighborhood of `s × t` in `α × β` includes
a product of an open neighborhood of `s` by an open neighborhood of `t`. -/
def NhdsContainBoxes (s : Set α) (t : Set β) : Prop :=
  ∀ n : Set (α × β), IsOpen n → (s ×ˢ t ⊆ n) →
    ∃ (u : Set α) (v : Set β), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n
#align nhds_contain_boxes NhdsContainBoxes

@[symm]
theorem NhdsContainBoxes.symm {s : Set α} {t : Set β} :
    NhdsContainBoxes s t → NhdsContainBoxes t s := fun H n hn hp =>
  let ⟨u, v, uo, vo, su, tv, p⟩ :=
    H (Prod.swap ⁻¹' n) (hn.preimage continuous_swap) (by rwa [← image_subset_iff, image_swap_prod])
  ⟨v, u, vo, uo, tv, su, by rwa [← image_subset_iff, image_swap_prod] at p⟩
#align nhds_contain_boxes.symm NhdsContainBoxes.symm

theorem NhdsContainBoxes.comm {s : Set α} {t : Set β} :
    NhdsContainBoxes s t ↔ NhdsContainBoxes t s :=
  Iff.intro NhdsContainBoxes.symm NhdsContainBoxes.symm
#align nhds_contain_boxes.comm NhdsContainBoxes.comm

theorem nhdsContainBoxes_of_singleton {x : α} {y : β} :
    NhdsContainBoxes ({x} : Set α) ({y} : Set β) := fun n hn hp =>
  let ⟨u, v, uo, vo, xu, yv, hp'⟩ := isOpen_prod_iff.mp hn x y (hp <| by simp)
  ⟨u, v, uo, vo, by simpa, by simpa, hp'⟩
#align nhds_contain_boxes_of_singleton nhdsContainBoxes_of_singleton

theorem nhdsContainBoxes_of_compact {s : Set α} (hs : IsCompact s) (t : Set β)
    (H : ∀ x ∈ s, NhdsContainBoxes ({x} : Set α) t) : NhdsContainBoxes s t := fun n hn hp =>
  have :
    ∀ x : s,
      ∃ uv : Set α × Set β, IsOpen uv.1 ∧ IsOpen uv.2 ∧ {↑x} ⊆ uv.1 ∧ t ⊆ uv.2 ∧ uv.1 ×ˢ uv.2 ⊆ n :=
    fun ⟨x, hx⟩ =>
    have : ({x} : Set α) ×ˢ t ⊆ n := Subset.trans (prod_mono (by simpa) Subset.rfl) hp
    let ⟨ux, vx, H1⟩ := H x hx n hn this
    ⟨⟨ux, vx⟩, H1⟩
  let ⟨uvs, h⟩ := Classical.axiom_of_choice this
  have us_cover : s ⊆ ⋃ i, (uvs i).1 := fun x hx =>
    subset_iUnion _ ⟨x, hx⟩ (by simpa using (h ⟨x, hx⟩).2.2.1)
  let ⟨s0, s0_cover⟩ := hs.elim_finite_subcover _ (fun i => (h i).1) us_cover
  let u := ⋃ i ∈ s0, (uvs i).1
  let v := ⋂ i ∈ s0, (uvs i).2
  have : IsOpen u := isOpen_biUnion fun i _ => (h i).1
  have : IsOpen v := isOpen_biInter s0.finite_toSet fun i _ => (h i).2.1
  have : t ⊆ v := subset_iInter₂ fun i _ => (h i).2.2.2.1
  have : u ×ˢ v ⊆ n := fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    have : ∃ i ∈ s0, x' ∈ (uvs i).1 := by simpa using hx'
    let ⟨i, is0, hi⟩ := this
    (h i).2.2.2.2 ⟨hi, (biInter_subset_of_mem is0 : v ⊆ (uvs i).2) hy'⟩
  ⟨u, v, ‹IsOpen u›, ‹IsOpen v›, s0_cover, ‹t ⊆ v›, ‹u ×ˢ v ⊆ n›⟩
#align nhds_contain_boxes_of_compact nhdsContainBoxes_of_compact

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`. -/
theorem generalized_tube_lemma {s : Set α} (hs : IsCompact s) {t : Set β} (ht : IsCompact t)
    {n : Set (α × β)} (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set α) (v : Set β), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n :=
  have := nhdsContainBoxes_of_compact hs t fun x _ => NhdsContainBoxes.symm <|
    nhdsContainBoxes_of_compact ht {x} fun _ _ => nhdsContainBoxes_of_singleton
  this n hn hp
#align generalized_tube_lemma generalized_tube_lemma

end TubeLemma

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
  isCompact_of_isClosed_subset isCompact_univ h (subset_univ _)
#align is_closed.is_compact IsClosed.isCompact

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

theorem exists_subset_nhds_of_compactSpace [CompactSpace α] {ι : Type*} [Nonempty ι]
    {V : ι → Set α} (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set α}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV (fun i => (hV_closed i).isCompact) hV_closed hU
#align exists_subset_nhds_of_compact_space exists_subset_nhds_of_compactSpace

/-- If `f : α → β` is an `Inducing` map, then the image `f '' s` of a set `s` is compact if and only
if the set `s` is closed. -/
theorem Inducing.isCompact_iff {f : α → β} (hf : Inducing f) {s : Set α} :
    IsCompact (f '' s) ↔ IsCompact s := by
  refine ⟨fun hs F F_ne_bot F_le => ?_, fun hs => hs.image hf.continuous⟩
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩
#align inducing.is_compact_iff Inducing.isCompact_iff

/-- If `f : α → β` is an `Embedding` (or more generally, an `Inducing` map, see
`Inducing.isCompact_iff`), then the image `f '' s` of a set `s` is compact if and only if the set
`s` is closed. -/
theorem Embedding.isCompact_iff_isCompact_image {f : α → β} (hf : Embedding f) :
    IsCompact s ↔ IsCompact (f '' s) :=
  hf.toInducing.isCompact_iff.symm
#align embedding.is_compact_iff_is_compact_image Embedding.isCompact_iff_isCompact_image

/-- The preimage of a compact set under a closed embedding is a compact set. -/
theorem ClosedEmbedding.isCompact_preimage {f : α → β} (hf : ClosedEmbedding f) {K : Set β}
    (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf.closed_range
  rwa [← hf.toInducing.isCompact_iff, image_preimage_eq_inter_range]
#align closed_embedding.is_compact_preimage ClosedEmbedding.isCompact_preimage

/-- A closed embedding is proper, ie, inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `ClosedEmbedding.isCompact_preimage`. -/
theorem ClosedEmbedding.tendsto_cocompact {f : α → β} (hf : ClosedEmbedding f) :
    Tendsto f (Filter.cocompact α) (Filter.cocompact β) :=
  Filter.hasBasis_cocompact.tendsto_right_iff.mpr fun _K hK =>
    (hf.isCompact_preimage hK).compl_mem_cocompact
#align closed_embedding.tendsto_cocompact ClosedEmbedding.tendsto_cocompact

theorem isCompact_iff_isCompact_in_subtype {p : α → Prop} {s : Set { a // p a }} :
    IsCompact s ↔ IsCompact (((↑) : _ → α) '' s) :=
  embedding_subtype_val.isCompact_iff_isCompact_image
#align is_compact_iff_is_compact_in_subtype isCompact_iff_isCompact_in_subtype

theorem isCompact_iff_isCompact_univ {s : Set α} : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [isCompact_iff_isCompact_in_subtype, image_univ, Subtype.range_coe]
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
  ⟨by rw [← hf.toInducing.isCompact_iff, image_univ]; exact hf.closed_range.isCompact⟩
#align closed_embedding.compact_space ClosedEmbedding.compactSpace

theorem IsCompact.prod {s : Set α} {t : Set β} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds] at hs ht ⊢
  intro f hfs
  rw [le_principal_iff] at hfs
  obtain ⟨a : α, sa : a ∈ s, ha : map Prod.fst f.1 ≤ 𝓝 a⟩ :=
    hs (f.map Prod.fst) (le_principal_iff.2 <| mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨b : β, tb : b ∈ t, hb : map Prod.snd f.1 ≤ 𝓝 b⟩ :=
    ht (f.map Prod.snd) (le_principal_iff.2 <| mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at ha hb
  refine' ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩
  rw [nhds_prod_eq]; exact le_inf ha hb
#align is_compact.prod IsCompact.prod

/-- Finite topological spaces are compact. -/
instance (priority := 100) Finite.compactSpace [Finite α] : CompactSpace α
    where isCompact_univ := finite_univ.isCompact
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
  ext S
  simp only [mem_coprod_iff, exists_prop, mem_comap, Filter.mem_cocompact]
  constructor
  · rintro ⟨⟨A, ⟨t, ht, hAt⟩, hAS⟩, B, ⟨t', ht', hBt'⟩, hBS⟩
    refine' ⟨t ×ˢ t', ht.prod ht', _⟩
    refine' Subset.trans _ (union_subset hAS hBS)
    rw [compl_subset_comm] at hAt hBt' ⊢
    refine' Subset.trans (fun x => _) (Set.prod_mono hAt hBt')
    simp only [compl_union, mem_inter_iff, mem_prod, mem_preimage, mem_compl_iff]
    tauto
  · rintro ⟨t, ht, htS⟩
    refine' ⟨⟨(Prod.fst '' t)ᶜ, _, _⟩, ⟨(Prod.snd '' t)ᶜ, _, _⟩⟩
    · exact ⟨Prod.fst '' t, ht.image continuous_fst, Subset.rfl⟩
    · rw [preimage_compl]
      rw [compl_subset_comm] at htS ⊢
      exact htS.trans (subset_preimage_image Prod.fst _)
    · exact ⟨Prod.snd '' t, ht.image continuous_snd, Subset.rfl⟩
    · rw [preimage_compl]
      rw [compl_subset_comm] at htS ⊢
      exact htS.trans (subset_preimage_image Prod.snd _)
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

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class LocallyCompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : α), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
#align locally_compact_space LocallyCompactSpace

theorem compact_basis_nhds [LocallyCompactSpace α] (x : α) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  hasBasis_self.2 <| by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x
#align compact_basis_nhds compact_basis_nhds

theorem local_compact_nhds [LocallyCompactSpace α] {x : α} {n : Set α} (h : n ∈ 𝓝 x) :
    ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h
#align local_compact_nhds local_compact_nhds

/-- In a locally compact space, the filters `𝓝 x` and `cocompact α` are disjoint for all `α`. -/
theorem disjoint_nhds_cocompact [LocallyCompactSpace α] (x : α) : Disjoint (𝓝 x) (cocompact α) :=
  let ⟨_, hx, _, hc⟩ := local_compact_nhds (univ_mem (f := 𝓝 x));
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

theorem locallyCompactSpace_of_hasBasis {ι : α → Type*} {p : ∀ x, ι x → Prop}
    {s : ∀ x, ι x → Set α} (h : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace α :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩
#align locally_compact_space_of_has_basis locallyCompactSpace_of_hasBasis

instance Prod.locallyCompactSpace (α : Type*) (β : Type*) [TopologicalSpace α]
    [TopologicalSpace β] [LocallyCompactSpace α] [LocallyCompactSpace β] :
    LocallyCompactSpace (α × β) :=
  have := fun x : α × β => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  locallyCompactSpace_of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂
#align prod.locally_compact_space Prod.locallyCompactSpace

section Pi

variable [∀ i, TopologicalSpace (π i)] [∀ i, LocallyCompactSpace (π i)]

/-- In general it suffices that all but finitely many of the spaces are compact,
  but that's not straightforward to state and use. -/
instance Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (∀ i, π i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine' ⟨(Set.univ : Set ι).pi n'', _, subset_trans (fun _ h => _) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩
#align pi.locally_compact_space_of_finite Pi.locallyCompactSpace_of_finite

/-- For spaces that are not Hausdorff. -/
instance Pi.locallyCompactSpace [∀ i, CompactSpace (π i)] : LocallyCompactSpace (∀ i, π i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine' ⟨s.pi n'', _, subset_trans (fun _ => _) hsub, _⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · rw [← Set.univ_pi_ite]
      refine' isCompact_univ_pi fun i => _
      by_cases h : i ∈ s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩
#align pi.locally_compact_space Pi.locallyCompactSpace

instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace β] :
    LocallyCompactSpace (ι → β) :=
  Pi.locallyCompactSpace_of_finite
#align function.locally_compact_space_of_finite Function.locallyCompactSpace_of_finite

instance Function.locallyCompactSpace [LocallyCompactSpace β] [CompactSpace β] :
    LocallyCompactSpace (ι → β) :=
  Pi.locallyCompactSpace
#align function.locally_compact_space Function.locallyCompactSpace

end Pi

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
theorem exists_compact_subset [LocallyCompactSpace α] {x : α} {U : Set α} (hU : IsOpen U)
    (hx : x ∈ U) : ∃ K : Set α, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩
#align exists_compact_subset exists_compact_subset

/-- In a locally compact space every point has a compact neighborhood. -/
theorem exists_compact_mem_nhds [LocallyCompactSpace α] (x : α) : ∃ K, IsCompact K ∧ K ∈ 𝓝 x :=
  let ⟨K, hKc, hx, _⟩ := exists_compact_subset isOpen_univ (mem_univ x)
  ⟨K, hKc, mem_interior_iff_mem_nhds.1 hx⟩
#align exists_compact_mem_nhds exists_compact_mem_nhds

/-- In a locally compact space, for every containment `K ⊆ U` of a compact set `K` in an open
  set `U`, there is a compact neighborhood `L` such that `K ⊆ L ⊆ U`: equivalently, there is a
  compact `L` such that `K ⊆ interior L` and `L ⊆ U`. -/
theorem exists_compact_between [hα : LocallyCompactSpace α] {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (h_KU : K ⊆ U) : ∃ L, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U := by
  choose V hVc hxV hKV using fun x : K => exists_compact_subset hU (h_KU x.2)
  have : K ⊆ ⋃ x, interior (V x) := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩
  rcases hK.elim_finite_subcover _ (fun x => @isOpen_interior α _ (V x)) this with ⟨t, ht⟩
  refine'
    ⟨_, t.isCompact_biUnion fun x _ => hVc x, fun x hx => _, Set.iUnion₂_subset fun i _ => hKV i⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hy⟩
  exact interior_mono (subset_iUnion₂ y hyt) hy
#align exists_compact_between exists_compact_between

/-- In a locally compact space, every compact set is contained in the interior of a compact set. -/
theorem exists_compact_superset [LocallyCompactSpace α] {K : Set α} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ interior K' :=
  let ⟨L, hLc, hKL, _⟩ := exists_compact_between hK isOpen_univ K.subset_univ
  ⟨L, hLc, hKL⟩
#align exists_compact_superset exists_compact_superset

protected theorem ClosedEmbedding.locallyCompactSpace [LocallyCompactSpace β] {f : α → β}
    (hf : ClosedEmbedding f) : LocallyCompactSpace α :=
  haveI : ∀ x : α, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (f x) ∧ IsCompact s) fun s => f ⁻¹' s := by
    intro x
    rw [hf.toInducing.nhds_eq_comap]
    exact (compact_basis_nhds _).comap _
  locallyCompactSpace_of_hasBasis this fun x s hs => hf.isCompact_preimage hs.2
#align closed_embedding.locally_compact_space ClosedEmbedding.locallyCompactSpace

protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace α] {s : Set α}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  (closedEmbedding_subtype_val hs).locallyCompactSpace
#align is_closed.locally_compact_space IsClosed.locallyCompactSpace

protected theorem OpenEmbedding.locallyCompactSpace [LocallyCompactSpace β] {f : α → β}
    (hf : OpenEmbedding f) : LocallyCompactSpace α := by
  have : ∀ x : α, (𝓝 x).HasBasis
      (fun s => (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ range f) fun s => f ⁻¹' s := by
    intro x
    rw [hf.toInducing.nhds_eq_comap]
    exact
      ((compact_basis_nhds _).restrict_subset <| hf.open_range.mem_nhds <| mem_range_self _).comap _
  refine' locallyCompactSpace_of_hasBasis this fun x s hs => _
  rw [← hf.toInducing.isCompact_iff, image_preimage_eq_of_subset hs.2]
  exact hs.1.2
#align open_embedding.locally_compact_space OpenEmbedding.locallyCompactSpace

protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace α] {s : Set α} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.openEmbedding_subtype_val.locallyCompactSpace
#align is_open.locally_compact_space IsOpen.locallyCompactSpace

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace α] (F : Ultrafilter α) : ↑F ≤ 𝓝 F.lim := by
  rcases isCompact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩
  exact le_nhds_lim ⟨x, h⟩
set_option linter.uppercaseLean3 false in
#align ultrafilter.le_nhds_Lim Ultrafilter.le_nhds_lim

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

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`. -/
class SigmaCompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a σ-compact space, there exists (by definition) a countable collection of compact subspaces
  that cover the entire space. -/
  exists_compact_covering : ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ
#align sigma_compact_space SigmaCompactSpace

-- see Note [lower instance priority]
instance (priority := 200) CompactSpace.sigma_compact [CompactSpace α] : SigmaCompactSpace α :=
  ⟨⟨fun _ => univ, fun _ => isCompact_univ, iUnion_const _⟩⟩
#align compact_space.sigma_compact CompactSpace.sigma_compact

theorem SigmaCompactSpace.of_countable (S : Set (Set α)) (Hc : S.Countable)
    (Hcomp : ∀ s ∈ S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace α :=
  ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩
#align sigma_compact_space.of_countable SigmaCompactSpace.of_countable

-- see Note [lower instance priority]
instance (priority := 100) sigmaCompactSpace_of_locally_compact_second_countable
    [LocallyCompactSpace α] [SecondCountableTopology α] : SigmaCompactSpace α := by
  choose K hKc hxK using fun x : α => exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine' SigmaCompactSpace.of_countable _ (hsc.image K) (ball_image_iff.2 fun x _ => hKc x) _
  rwa [sUnion_image]
#align sigma_compact_space_of_locally_compact_second_countable sigmaCompactSpace_of_locally_compact_second_countable

-- porting note: doesn't work on the same line
variable (α)
variable [SigmaCompactSpace α]

open SigmaCompactSpace

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
def compactCovering : ℕ → Set α :=
  Accumulate exists_compact_covering.choose
#align compact_covering compactCovering

theorem isCompact_compactCovering (n : ℕ) : IsCompact (compactCovering α n) :=
  isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n
#align is_compact_compact_covering isCompact_compactCovering

theorem iUnion_compactCovering : ⋃ n, compactCovering α n = univ := by
  rw [compactCovering, iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2
#align Union_compact_covering iUnion_compactCovering

@[mono]
theorem compactCovering_subset ⦃m n : ℕ⦄ (h : m ≤ n) : compactCovering α m ⊆ compactCovering α n :=
  monotone_accumulate h
#align compact_covering_subset compactCovering_subset

variable {α}

theorem exists_mem_compactCovering (x : α) : ∃ n, x ∈ compactCovering α n :=
  iUnion_eq_univ_iff.mp (iUnion_compactCovering α) x
#align exists_mem_compact_covering exists_mem_compactCovering

instance [SigmaCompactSpace β] : SigmaCompactSpace (α × β) :=
  ⟨⟨fun n => compactCovering α n ×ˢ compactCovering β n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset α) (compactCovering_subset β),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

instance [Finite ι] [∀ i, TopologicalSpace (π i)] [∀ i, SigmaCompactSpace (π i)] :
    SigmaCompactSpace (∀ i, π i) := by
  refine' ⟨⟨fun n => Set.pi univ fun i => compactCovering (π i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (π i) _, _⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (π i)

instance [SigmaCompactSpace β] : SigmaCompactSpace (Sum α β) :=
  ⟨⟨fun n => Sum.inl '' compactCovering α n ∪ Sum.inr '' compactCovering β n, fun n =>
      ((isCompact_compactCovering α n).image continuous_inl).union
        ((isCompact_compactCovering β n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_inl_union_range_inr]⟩⟩

instance [Countable ι] [∀ i, TopologicalSpace (π i)] [∀ i, SigmaCompactSpace (π i)] :
    SigmaCompactSpace (Σi, π i) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine' ⟨⟨fun n => ⋃ k ≤ n, Sigma.mk (f k) '' compactCovering (π (f k)) n, fun n => _, _⟩⟩
    · refine' (finite_le_nat _).isCompact_biUnion fun k _ => _
      exact (isCompact_compactCovering _ _).image continuous_sigmaMk
    · simp only [iUnion_eq_univ_iff, Sigma.forall, mem_iUnion]
      rw [hf.forall] -- porting note: `simp only` failed to use `hf.forall`
      intro k y
      rcases exists_mem_compactCovering y with ⟨n, hn⟩
      refine' ⟨max k n, k, le_max_left _ _, mem_image_of_mem _ _⟩
      exact compactCovering_subset _ (le_max_right _ _) hn

protected theorem ClosedEmbedding.sigmaCompactSpace {e : β → α} (he : ClosedEmbedding e) :
    SigmaCompactSpace β :=
  ⟨⟨fun n => e ⁻¹' compactCovering α n, fun n =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
#align closed_embedding.sigma_compact_space ClosedEmbedding.sigmaCompactSpace

-- porting note: new lemma
theorem IsClosed.sigmaCompactSpace {s : Set α} (hs : IsClosed s) : SigmaCompactSpace s :=
  (closedEmbedding_subtype_val hs).sigmaCompactSpace

instance [SigmaCompactSpace β] : SigmaCompactSpace (ULift.{u} β) :=
  ULift.closedEmbedding_down.sigmaCompactSpace

/-- If `α` is a `σ`-compact space, then a locally finite family of nonempty sets of `α` can have
only countably many elements, `Set.Countable` version. -/
protected theorem LocallyFinite.countable_univ {ι : Type*} {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Countable := by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering α n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩
#align locally_finite.countable_univ LocallyFinite.countable_univ

/-- If `f : ι → Set α` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
protected noncomputable def LocallyFinite.encodable {ι : Type*} {f : ι → Set α}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm
#align locally_finite.encodable LocallyFinite.encodable

/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
theorem countable_cover_nhdsWithin_of_sigma_compact {f : α → Set α} {s : Set α} (hs : IsClosed s)
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ (t : _) (_ : t ⊆ s), t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering α n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine'
    ⟨⋃ n, (t n : Set α), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n).countable_toSet, fun x hx => mem_iUnion₂.2 _⟩
  rcases exists_mem_compactCovering x with ⟨n, hn⟩
  rcases mem_iUnion₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩
  exact ⟨y, mem_iUnion.2 ⟨n, hyt⟩, hyf hx⟩
#align countable_cover_nhds_within_of_sigma_compact countable_cover_nhdsWithin_of_sigma_compact

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds_of_sigma_compact {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigma_compact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
#align countable_cover_nhds_of_sigma_compact countable_cover_nhds_of_sigma_compact

end Compact

/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`⋃ n, K n = univ`.

If `X` is a locally compact sigma compact space, then `CompactExhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : CompactExhaustion X)`. -/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : ℕ → Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : ∀ n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
    each set is contained in the interior of the next. -/
  subset_interior_succ' : ∀ n, toFun n ⊆ interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ
#align compact_exhaustion CompactExhaustion

namespace CompactExhaustion

instance : @RelHomClass (CompactExhaustion α) ℕ (Set α) LE.le HasSubset.Subset where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
  map_rel f _ _ h := monotone_nat_of_le_succ
    (fun n ↦ (f.subset_interior_succ' n).trans interior_subset) h

variable (K : CompactExhaustion α)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem isCompact (n : ℕ) : IsCompact (K n) :=
  K.isCompact' n
#align compact_exhaustion.is_compact CompactExhaustion.isCompact

theorem subset_interior_succ (n : ℕ) : K n ⊆ interior (K (n + 1)) :=
  K.subset_interior_succ' n
#align compact_exhaustion.subset_interior_succ CompactExhaustion.subset_interior_succ

@[mono]
protected theorem subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h
#align compact_exhaustion.subset CompactExhaustion.subset

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset n.le_succ
#align compact_exhaustion.subset_succ CompactExhaustion.subset_succ

theorem subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ interior (K n) :=
  Subset.trans (K.subset_interior_succ m) <| interior_mono <| K.subset h
#align compact_exhaustion.subset_interior CompactExhaustion.subset_interior

theorem iUnion_eq : ⋃ n, K n = univ :=
  K.iUnion_eq'
#align compact_exhaustion.Union_eq CompactExhaustion.iUnion_eq

theorem exists_mem (x : α) : ∃ n, x ∈ K n :=
  iUnion_eq_univ_iff.1 K.iUnion_eq x
#align compact_exhaustion.exists_mem CompactExhaustion.exists_mem

/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : α) : ℕ :=
  Nat.find (K.exists_mem x)
#align compact_exhaustion.find CompactExhaustion.find

theorem mem_find (x : α) : x ∈ K (K.find x) :=
  Nat.find_spec (K.exists_mem x)
#align compact_exhaustion.mem_find CompactExhaustion.mem_find

theorem mem_iff_find_le {x : α} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n :=
  ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h <| K.mem_find x⟩
#align compact_exhaustion.mem_iff_find_le CompactExhaustion.mem_iff_find_le

/-- Prepend the empty set to a compact exhaustion `K n`. -/
def shiftr : CompactExhaustion α where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩
#align compact_exhaustion.shiftr CompactExhaustion.shiftr

@[simp]
theorem find_shiftr (x : α) : K.shiftr.find x = K.find x + 1 :=
  Nat.find_comp_succ _ _ (not_mem_empty _)
#align compact_exhaustion.find_shiftr CompactExhaustion.find_shiftr

theorem mem_diff_shiftr_find (x : α) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
    mt K.shiftr.mem_iff_find_le.1 <| by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩
#align compact_exhaustion.mem_diff_shiftr_find CompactExhaustion.mem_diff_shiftr_find

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a locally compact sigma compact space. -/
noncomputable def choice (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose ∪ compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine' ⟨⟨fun n => (K n).1, fun n => (K n).2, fun n => _, _⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono <| subset_union_left _ _)
  · refine' univ_subset_iff.1 (iUnion_compactCovering X ▸ _)
    exact iUnion_mono' fun n => ⟨n + 1, subset_union_right _ _⟩
#align compact_exhaustion.choice CompactExhaustion.choice

noncomputable instance [LocallyCompactSpace α] [SigmaCompactSpace α] :
    Inhabited (CompactExhaustion α) :=
  ⟨CompactExhaustion.choice α⟩

end CompactExhaustion

section Clopen

-- porting note: definition moved to `Mathlib.Topology.Basic`

theorem isClopen_iff_frontier_eq_empty {s : Set α} : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, diff_eq_empty]
  refine' ⟨fun h => (h.2.trans h.1.symm).subset, fun h => _⟩
  exact ⟨interior_subset.antisymm (subset_closure.trans h),
    (h.trans interior_subset).antisymm subset_closure⟩
#align is_clopen_iff_frontier_eq_empty isClopen_iff_frontier_eq_empty

alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty
#align is_clopen.frontier_eq IsClopen.frontier_eq

theorem IsClopen.union {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩
#align is_clopen.union IsClopen.union

theorem IsClopen.inter {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
#align is_clopen.inter IsClopen.inter

@[simp] theorem isClopen_empty : IsClopen (∅ : Set α) := ⟨isOpen_empty, isClosed_empty⟩
#align is_clopen_empty isClopen_empty

@[simp] theorem isClopen_univ : IsClopen (univ : Set α) := ⟨isOpen_univ, isClosed_univ⟩
#align is_clopen_univ isClopen_univ

theorem IsClopen.compl {s : Set α} (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isOpen_compl, hs.1.isClosed_compl⟩
#align is_clopen.compl IsClopen.compl

@[simp]
theorem isClopen_compl_iff {s : Set α} : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩
#align is_clopen_compl_iff isClopen_compl_iff

theorem IsClopen.diff {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl
#align is_clopen.diff IsClopen.diff

theorem IsClopen.prod {s : Set α} {t : Set β} (hs : IsClopen s) (ht : IsClopen t) :
    IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
#align is_clopen.prod IsClopen.prod

theorem isClopen_iUnion {β : Type*} [Finite β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isOpen_iUnion (forall_and.1 h).1, isClosed_iUnion (forall_and.1 h).2⟩
#align is_clopen_Union isClopen_iUnion

theorem isClopen_biUnion {β : Type*} {s : Set β} {f : β → Set α} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  ⟨isOpen_biUnion fun i hi => (h i hi).1, isClosed_biUnion hs fun i hi => (h i hi).2⟩
#align is_clopen_bUnion isClopen_biUnion

theorem isClopen_biUnion_finset {β : Type*} {s : Finset β} {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  isClopen_biUnion s.finite_toSet h
#align is_clopen_bUnion_finset isClopen_biUnion_finset

theorem isClopen_iInter {β : Type*} [Finite β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isOpen_iInter (forall_and.1 h).1, isClosed_iInter (forall_and.1 h).2⟩
#align is_clopen_Inter isClopen_iInter

theorem isClopen_biInter {β : Type*} {s : Set β} (hs : s.Finite) {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  ⟨isOpen_biInter hs fun i hi => (h i hi).1, isClosed_biInter fun i hi => (h i hi).2⟩
#align is_clopen_bInter isClopen_biInter

theorem isClopen_biInter_finset {β : Type*} {s : Finset β} {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  isClopen_biInter s.finite_toSet h
#align is_clopen_bInter_finset isClopen_biInter_finset

theorem IsClopen.preimage {s : Set β} (h : IsClopen s) {f : α → β} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩
#align is_clopen.preimage IsClopen.preimage

theorem ContinuousOn.preimage_clopen_of_clopen {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_open_of_open hf hs.1 ht.1,
    ContinuousOn.preimage_closed_of_closed hf hs.2 ht.2⟩
#align continuous_on.preimage_clopen_of_clopen ContinuousOn.preimage_clopen_of_clopen

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem isClopen_inter_of_disjoint_cover_clopen {Z a b : Set α} (h : IsClopen Z) (cover : Z ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (Z ∩ a) := by
  refine' ⟨IsOpen.inter h.1 ha, _⟩
  have : IsClosed (Z ∩ bᶜ) := IsClosed.inter h.2 (isClosed_compl_iff.2 hb)
  convert this using 1
  refine' (inter_subset_inter_right Z hab.subset_compl_right).antisymm _
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩
#align is_clopen_inter_of_disjoint_cover_clopen isClopen_inter_of_disjoint_cover_clopen

@[simp]
theorem isClopen_discrete [DiscreteTopology α] (x : Set α) : IsClopen x :=
  ⟨isOpen_discrete _, isClosed_discrete _⟩
#align is_clopen_discrete isClopen_discrete

-- porting note: new lemma
theorem isClopen_range_inl : IsClopen (range (Sum.inl : α → α ⊕ β)) :=
  ⟨isOpen_range_inl, isClosed_range_inl⟩

-- porting note: new lemma
theorem isClopen_range_inr : IsClopen (range (Sum.inr : β → α ⊕ β)) :=
  ⟨isOpen_range_inr, isClosed_range_inr⟩

theorem isClopen_range_sigmaMk {ι : Type*} {σ : ι → Type*} [∀ i, TopologicalSpace (σ i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι σ i)) :=
  ⟨openEmbedding_sigmaMk.open_range, closedEmbedding_sigmaMk.closed_range⟩
#align clopen_range_sigma_mk isClopen_range_sigmaMk

protected theorem QuotientMap.isClopen_preimage {f : α → β} (hf : QuotientMap f) {s : Set β} :
    IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isOpen_preimage hf.isClosed_preimage
#align quotient_map.is_clopen_preimage QuotientMap.isClopen_preimage

variable {X : Type*} [TopologicalSpace X]

theorem continuous_boolIndicator_iff_clopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  rw [continuous_to_bool, preimage_boolIndicator_true]
#align continuous_bool_indicator_iff_clopen continuous_boolIndicator_iff_clopen

theorem continuousOn_boolIndicator_iff_clopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s → X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_restrict, ← continuous_boolIndicator_iff_clopen]
  rfl
#align continuous_on_indicator_iff_clopen continuousOn_boolIndicator_iff_clopen

end Clopen

section Preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def IsPreirreducible (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty
#align is_preirreducible IsPreirreducible

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def IsIrreducible (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreirreducible s
#align is_irreducible IsIrreducible

theorem IsIrreducible.nonempty {s : Set α} (h : IsIrreducible s) : s.Nonempty :=
  h.1
#align is_irreducible.nonempty IsIrreducible.nonempty

theorem IsIrreducible.isPreirreducible {s : Set α} (h : IsIrreducible s) : IsPreirreducible s :=
  h.2
#align is_irreducible.is_preirreducible IsIrreducible.isPreirreducible

theorem isPreirreducible_empty : IsPreirreducible (∅ : Set α) := fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim
#align is_preirreducible_empty isPreirreducible_empty

theorem Set.Subsingleton.isPreirreducible {s : Set α} (hs : s.Subsingleton) : IsPreirreducible s :=
  fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩
#align set.subsingleton.is_preirreducible Set.Subsingleton.isPreirreducible

-- porting note: new lemma
theorem isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set α) :=
  subsingleton_singleton.isPreirreducible

theorem isIrreducible_singleton {x} : IsIrreducible ({x} : Set α) :=
  ⟨singleton_nonempty x, isPreirreducible_singleton⟩
#align is_irreducible_singleton isIrreducible_singleton

theorem isPreirreducible_iff_closure {s : Set α} :
    IsPreirreducible (closure s) ↔ IsPreirreducible s :=
  forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]
#align is_preirreducible_iff_closure isPreirreducible_iff_closure

theorem isIrreducible_iff_closure {s : Set α} : IsIrreducible (closure s) ↔ IsIrreducible s :=
  and_congr closure_nonempty_iff isPreirreducible_iff_closure
#align is_irreducible_iff_closure isIrreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure
#align is_preirreducible.closure IsPreirreducible.closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure
#align is_irreducible.closure IsIrreducible.closure

theorem exists_preirreducible (s : Set α) (H : IsPreirreducible s) :
    ∃ t : Set α, IsPreirreducible t ∧ s ⊆ t ∧ ∀ u, IsPreirreducible u → t ⊆ u → u = t :=
  let ⟨m, hm, hsm, hmm⟩ :=
    zorn_subset_nonempty { t : Set α | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hzq⟩ := mem_sUnion.1 hz
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨z, hzq, hzv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨z, hqp hzq, hzv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm, hsm, fun _u hu hmu => hmm _ hu hmu⟩
#align exists_preirreducible exists_preirreducible

/-- The set of irreducible components of a topological space. -/
def irreducibleComponents (α : Type*) [TopologicalSpace α] : Set (Set α) :=
  maximals (· ≤ ·) { s : Set α | IsIrreducible s }
#align irreducible_components irreducibleComponents

theorem isClosed_of_mem_irreducibleComponents (s) (H : s ∈ irreducibleComponents α) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed, eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)
#align is_closed_of_mem_irreducible_components isClosed_of_mem_irreducibleComponents

theorem irreducibleComponents_eq_maximals_closed (α : Type*) [TopologicalSpace α] :
    irreducibleComponents α = maximals (· ≤ ·) { s : Set α | IsClosed s ∧ IsIrreducible s } := by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine' ⟨H.1.2, fun x h e => _⟩
    have : closure x ≤ s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this
#align irreducible_components_eq_maximals_closed irreducibleComponents_eq_maximals_closed

/-- A maximal irreducible set that contains a given point. -/
def irreducibleComponent (x : α) : Set α :=
  Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)
#align irreducible_component irreducibleComponent

theorem irreducibleComponent_property (x : α) :
    IsPreirreducible (irreducibleComponent x) ∧
      {x} ⊆ irreducibleComponent x ∧
        ∀ u, IsPreirreducible u → irreducibleComponent x ⊆ u → u = irreducibleComponent x :=
  Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)
#align irreducible_component_property irreducibleComponent_property

theorem mem_irreducibleComponent {x : α} : x ∈ irreducibleComponent x :=
  singleton_subset_iff.1 (irreducibleComponent_property x).2.1
#align mem_irreducible_component mem_irreducibleComponent

theorem isIrreducible_irreducibleComponent {x : α} : IsIrreducible (irreducibleComponent x) :=
  ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩
#align is_irreducible_irreducible_component isIrreducible_irreducibleComponent

theorem eq_irreducibleComponent {x : α} {s : Set α} :
    IsPreirreducible s → irreducibleComponent x ⊆ s → s = irreducibleComponent x :=
  (irreducibleComponent_property x).2.2 _
#align eq_irreducible_component eq_irreducibleComponent

theorem irreducibleComponent_mem_irreducibleComponents (x : α) :
    irreducibleComponent x ∈ irreducibleComponents α :=
  ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩
#align irreducible_component_mem_irreducible_components irreducibleComponent_mem_irreducibleComponents

theorem isClosed_irreducibleComponent {x : α} : IsClosed (irreducibleComponent x) :=
  isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)
#align is_closed_irreducible_component isClosed_irreducibleComponent

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class PreirreducibleSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- In a preirreducible space, `Set.univ` is a preirreducible set. -/
  isPreirreducible_univ : IsPreirreducible (univ : Set α)
#align preirreducible_space PreirreducibleSpace

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class IrreducibleSpace (α : Type u) [TopologicalSpace α] extends PreirreducibleSpace α : Prop where
  toNonempty : Nonempty α
#align irreducible_space IrreducibleSpace

-- see Note [lower instance priority]
attribute [instance 50] IrreducibleSpace.toNonempty

theorem IrreducibleSpace.isIrreducible_univ (α : Type u) [TopologicalSpace α] [IrreducibleSpace α] :
    IsIrreducible (univ : Set α) :=
  ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
#align irreducible_space.is_irreducible_univ IrreducibleSpace.isIrreducible_univ

theorem irreducibleSpace_def (α : Type u) [TopologicalSpace α] :
    IrreducibleSpace α ↔ IsIrreducible (⊤ : Set α) :=
  ⟨@IrreducibleSpace.isIrreducible_univ α _, fun h =>
    haveI : PreirreducibleSpace α := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩
#align irreducible_space_def irreducibleSpace_def

theorem nonempty_preirreducible_inter [PreirreducibleSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ α _ _ s t
#align nonempty_preirreducible_inter nonempty_preirreducible_inter

/-- In a (pre)irreducible space, a nonempty open set is dense. -/
protected theorem IsOpen.dense [PreirreducibleSpace α] {s : Set α} (ho : IsOpen s)
    (hne : s.Nonempty) : Dense s :=
  dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne
#align is_open.dense IsOpen.dense

theorem IsPreirreducible.image {s : Set α} (H : IsPreirreducible s) (f : α → β)
    (hf : ContinuousOn f s) : IsPreirreducible (f '' s) := by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u', ← u'_eq] at this
  rw [inter_comm s v', ← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨z, hzs, hzu', hzv'⟩
  refine' ⟨f z, mem_image_of_mem f hzs, _, _⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show z ∈ _ ∩ s
    simp [*]
#align is_preirreducible.image IsPreirreducible.image

theorem IsIrreducible.image {s : Set α} (H : IsIrreducible s) (f : α → β) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩
#align is_irreducible.image IsIrreducible.image

theorem Subtype.preirreducibleSpace {s : Set α} (h : IsPreirreducible s) :
    PreirreducibleSpace s where
  isPreirreducible_univ := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩
    exact ⟨⟨z, hzs⟩, ⟨Set.mem_univ _, ⟨hzu, hzv⟩⟩⟩
#align subtype.preirreducible_space Subtype.preirreducibleSpace

theorem Subtype.irreducibleSpace {s : Set α} (h : IsIrreducible s) : IrreducibleSpace s where
  isPreirreducible_univ :=
    (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype
#align subtype.irreducible_space Subtype.irreducibleSpace

/-- An infinite type with cofinite topology is an irreducible topological space. -/
instance (priority := 100) {α} [Infinite α] : IrreducibleSpace (CofiniteTopology α) where
  isPreirreducible_univ u v := by
    haveI : Infinite (CofiniteTopology α) := ‹_›
    simp only [CofiniteTopology.isOpen_iff, univ_inter]
    intro hu hv hu' hv'
    simpa only [compl_union, compl_compl] using ((hu hu').union (hv hv')).infinite_compl.nonempty
  toNonempty := (inferInstance : Nonempty α)

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
theorem isIrreducible_iff_sInter {s : Set α} :
    IsIrreducible s ↔
      ∀ (U : Finset (Set α)), (∀ u ∈ U, IsOpen u) → (∀ u ∈ U, (s ∩ u).Nonempty) →
        (s ∩ ⋂₀ ↑U).Nonempty := by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on
    case empty => simpa using h.nonempty
    case insert u U _ IH =>
      rw [Finset.coe_insert, sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (isOpen_sInter U.finite_toSet hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}
#align is_irreducible_iff_sInter isIrreducible_iff_sInter

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
theorem isPreirreducible_iff_closed_union_closed {s : Set α} :
    IsPreirreducible s ↔
      ∀ z₁ z₂ : Set α, IsClosed z₁ → IsClosed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := by
  refine compl_surjective.forall.trans <| forall_congr' fun z₁ => compl_surjective.forall.trans <|
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp, ← not_or, not_imp_not]
#align is_preirreducible_iff_closed_union_closed isPreirreducible_iff_closed_union_closed

/-- A set is irreducible if and only if for every cover by a finite collection of closed sets, it is
contained in one of the members of the collection. -/
theorem isIrreducible_iff_sUnion_closed {s : Set α} :
    IsIrreducible s ↔
      ∀ Z : Finset (Set α), (∀ z ∈ Z, IsClosed z) → (s ⊆ ⋃₀ ↑Z) → ∃ z ∈ Z, s ⊆ z := by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set α) _).toPerm _).finsetCongr.forall_congr fun {Z} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]
#align is_irreducible_iff_sUnion_closed isIrreducible_iff_sUnion_closed

/-- A nonempty open subset of a preirreducible subspace is dense in the subspace. -/
theorem subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set α} (hS : IsPreirreducible S)
    (hU : IsOpen U) (h : (S ∩ U).Nonempty) : S ⊆ closure (S ∩ U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S ∩ U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)
#align subset_closure_inter_of_is_preirreducible_of_is_open subset_closure_inter_of_isPreirreducible_of_isOpen

/-- If `∅ ≠ U ⊆ S ⊆ Z` such that `U` is open and `Z` is preirreducible, then `S` is irreducible. -/
theorem IsPreirreducible.subset_irreducible {S U Z : Set α} (hZ : IsPreirreducible Z)
    (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U ⊆ S) (h₂ : S ⊆ Z) : IsIrreducible S := by
  obtain ⟨z, hz⟩ := hU
  replace hZ : IsIrreducible Z := ⟨⟨z, h₂ (h₁ hz)⟩, hZ⟩
  refine' ⟨⟨z, h₁ hz⟩, _⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨a, -, ha'⟩ : Set.Nonempty (Z ∩ ⋂₀ ↑({U, u, v} : Finset (Set α)))
  · refine isIrreducible_iff_sInter.mp hZ {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace ha' : a ∈ U ∧ a ∈ u ∧ a ∈ v := by simpa using ha'
  exact ⟨a, h₁ ha'.1, ha'.2⟩
#align is_preirreducible.subset_irreducible IsPreirreducible.subset_irreducible

theorem IsPreirreducible.open_subset {Z U : Set α} (hZ : IsPreirreducible Z) (hU : IsOpen U)
    (hU' : U ⊆ Z) : IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (hZ.subset_irreducible h hU (fun _ => id) hU').2
#align is_preirreducible.open_subset IsPreirreducible.open_subset

theorem IsPreirreducible.interior {Z : Set α} (hZ : IsPreirreducible Z) :
    IsPreirreducible (interior Z) :=
  hZ.open_subset isOpen_interior interior_subset
#align is_preirreducible.interior IsPreirreducible.interior

theorem IsPreirreducible.preimage {Z : Set α} (hZ : IsPreirreducible Z) {f : β → α}
    (hf : OpenEmbedding f) : IsPreirreducible (f ⁻¹' Z) := by
  rintro U V hU hV ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨_, h₁, ⟨z, h₂, rfl⟩, ⟨z', h₃, h₄⟩⟩ :=
    hZ _ _ (hf.isOpenMap _ hU) (hf.isOpenMap _ hV) ⟨f x, hx, Set.mem_image_of_mem f hx'⟩
      ⟨f y, hy, Set.mem_image_of_mem f hy'⟩
  cases hf.inj h₄
  exact ⟨z, h₁, h₂, h₃⟩
#align is_preirreducible.preimage IsPreirreducible.preimage

end Preirreducible
