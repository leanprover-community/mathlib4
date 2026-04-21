/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousOn

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : α → Set β} {s : Set α} {x : α}

/-! ### Basic facts -/

lemma upperHemicontinuousWithinAt_iff_forall_isOpen :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  rw [upperHemicontinuousWithinAt_iff, hasBasis_nhdsSet _ |>.forall_iff ?mono]
  case mono => exact fun t₁ t₂ ht h ↦ h.mp <| .of_forall fun x' ↦ by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicontinuousWithinAt.forall_isOpen, UpperHemicontinuousWithinAt.of_forall_isOpen⟩ :=
  upperHemicontinuousWithinAt_iff_forall_isOpen

lemma upperHemicontinuousOn_iff_forall_isOpen :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=
  upperHemicontinuousOn_iff_forall_isOpen

lemma upperHemicontinuousAt_iff_forall_isOpen :
    UpperHemicontinuousAt f x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=
  upperHemicontinuousAt_iff_forall_isOpen

lemma upperHemicontinuous_iff_forall_isOpen :
    UpperHemicontinuous f ↔ ∀ x u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=
  upperHemicontinuous_iff_forall_isOpen

/-! ### Characterization in terms of preimages of intervals of sets -/

lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁, hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
    exact hst
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ ↦ ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]

lemma upperHemicontinuousAt_iff_preimage_Iic :
    UpperHemicontinuousAt f x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

lemma upperHemicontinuousOn_iff_preimage_Iic :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

lemma upperHemicontinuous_iff_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ x, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends open sets
to open sets. -/
lemma upperHemicontinuous_iff_isOpen_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic u)) := by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' (Iic _))]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff <|
      fun s t hst ↦ by gcongr; exact hst]
  simp [forall_comm (α := α)]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends closed sets to closed sets. -/
lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl :
    UpperHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic uᶜ))ᶜ := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

lemma isClosedMap_iff_upperHemicontinuous {f : α → β} :
    IsClosedMap f ↔ UpperHemicontinuous (f ⁻¹' {·}) := by
  rw [isClosedMap_iff_kernImage, upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends open sets to open sets. -/
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic uᶜ))ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, this, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_setOf, Filter.Eventually]

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends closed sets
to closed sets. -/
lemma lowerHemicontinuous_iff_isClosed_preimage_Iic :
    LowerHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic u)) := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

lemma isOpenMap_iff_lowerHemicontinuous {f : α → β} :
    IsOpenMap f ↔ LowerHemicontinuous (f ⁻¹' {·}) := by
  rw [isOpenMap_iff_kernImage, lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

/-! ### Singleton maps -/

lemma upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α → Set α) := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]
lemma upperHemicontinuousWithinAt_singleton_iff {f : α → β} {s : Set α} {x : α} :
    UpperHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf ↦ upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _ |>.comp hf
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exact mem_of_mem_nhds

@[simp]
lemma upperHemicontinuousAt_singleton_iff {f : α → β} {x : α} :
    UpperHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

@[simp]
lemma upperHemicontinuousOn_singleton_iff {f : α → β} {s : Set α} :
    UpperHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
  forall₂_congr <| fun _ _ ↦ upperHemicontinuousWithinAt_singleton_iff

@[simp]
lemma upperHemicontinuous_singleton_iff {f : α → β} :
    UpperHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← upperHemicontinuousOn_univ_iff]


/-! ### Union and intersection, and post-composition with the preimage map -/

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : α → Set β} {s : Set α} {x : α}

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
lemma UpperHemicontinuousWithinAt.union (hf : UpperHemicontinuousWithinAt f s x)
    (hg : UpperHemicontinuousWithinAt g s x) :
    UpperHemicontinuousWithinAt (fun x ↦ f x ∪ g x) s x := by
  rw [upperHemicontinuousWithinAt_iff] at hf hg ⊢
  aesop

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
lemma UpperHemicontinuousOn.union (hf : UpperHemicontinuousOn f s)
    (hg : UpperHemicontinuousOn g s) : UpperHemicontinuousOn (fun x ↦ f x ∪ g x) s := by
  rw [upperHemicontinuousOn_iff] at hf hg ⊢
  exact fun x hx ↦ (hf x hx).union (hg x hx)

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
lemma UpperHemicontinuousAt.union (hf : UpperHemicontinuousAt f x)
    (hg : UpperHemicontinuousAt g x) :
    UpperHemicontinuousAt (fun x ↦ f x ∪ g x) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.union hg

/-- Pointwise unions of upper hemicontinuous maps are upper hemicontinuous. -/
lemma UpperHemicontinuous.union (hf : UpperHemicontinuous f) (hg : UpperHemicontinuous g) :
    UpperHemicontinuous (fun x ↦ f x ∪ g x) := by
  rw [upperHemicontinuous_iff] at hf hg ⊢
  exact fun x ↦ (hf x).union (hg x)

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
lemma UpperHemicontinuousWithinAt.inter (hf : UpperHemicontinuousWithinAt f s x)
    {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousWithinAt (fun x ↦ f x ∩ u) s x := by
  rw [upperHemicontinuousWithinAt_iff_forall_isOpen] at hf ⊢
  intro t ht_open ht
  specialize hf (t ∪ uᶜ) (ht_open.union hu.isOpen_compl) (by grind)
  grind

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
lemma UpperHemicontinuousOn.inter (hf : UpperHemicontinuousOn f s) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousOn (fun x ↦ f x ∩ u) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact (hf · · |>.inter hu)

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
lemma UpperHemicontinuousAt.inter (hf : UpperHemicontinuousAt f x) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousAt (fun x ↦ f x ∩ u) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

/-- The pointwise intersection of an upper hemicontinuous function with a fixed closed set is
upper hemicontinuous. -/
lemma UpperHemicontinuous.inter (hf : UpperHemicontinuous f) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuous (fun x ↦ f x ∩ u) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x ↦ (hf x).inter hu

section Inducing

variable {γ : Type*} [TopologicalSpace γ] {i : γ → β}

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
lemma UpperHemicontinuousWithinAt.isInducing_comp (hf : UpperHemicontinuousWithinAt f s x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousWithinAt (fun x ↦ i ⁻¹' (f x)) s x := by
  refine .of_forall_isOpen fun u hu hifu ↦ ?_
  obtain ⟨v, hv, rfl⟩ := hi.isOpen_iff.mp hu
  simp_rw [← preimage_inter_range (s := f _), preimage_subset_preimage_iff inter_subset_right]
    at hifu ⊢
  exact hf.inter h_cl |>.forall_isOpen v hv hifu

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
lemma UpperHemicontinuousOn.isInducing_comp (hf : UpperHemicontinuousOn f s)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousOn (fun x ↦ i ⁻¹' (f x)) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact fun x hx ↦ (hf x hx).isInducing_comp hi h_cl

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
lemma UpperHemicontinuousAt.isInducing_comp (hf : UpperHemicontinuousAt f x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousAt (fun x ↦ i ⁻¹' (f x)) x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    hf.upperHemicontinuousWithinAt (s := Set.univ) |>.isInducing_comp hi h_cl

/-- Post-composition with the preimage of an inducing function whose range is closed preserves
upper hemicontinuity. -/
lemma UpperHemicontinuous.isInducing_comp (hf : UpperHemicontinuous f)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuous (fun x ↦ i ⁻¹' (f x)) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x ↦ (hf x).isInducing_comp hi h_cl

end Inducing

/-- Upper hemicontinuous functions always have closed domain.

The more general fact is that if `f` is upper hemicontinuous at `x₀` within `s`, and if
`x₀` is a cluster point of `s ∩ {x | (f x).Nonempty}`, then `(f x₀).Nonempty`. -/
lemma UpperHemicontinuous.isClosed_domain {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → Set β} (hf : UpperHemicontinuous f) :
    IsClosed {x | (f x).Nonempty} := by
  simp only [← isOpen_compl_iff, compl_setOf, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using hf x ∅

/-! ### Sequential characterizations -/

/-- **Sequential characterization of upper hemicontinuity**:
A set-valued function `f : α → Set β` is upper hemicontinuous at `x₀ : α` if for every pair
of sequences `x : ℕ → α` and `y : ℕ → β` such that `x` tends to `x₀` and `y n ∈ f (x n)` and
`y` tends to `y₀ : β`, then `y₀ ∈ f x₀`. This requires that there is some (sequentially) compact
set containing all `f x'` for `x'` sufficiently close to `x`.

This is a partial converse of `UpperHemicontinuousAt.mem_of_tendsto`. -/
lemma UpperHemicontinuousAt.of_sequences {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → Set β} {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    {K : Set β} (hK : IsSeqCompact K) (hf : ∀ᶠ x in 𝓝 x₀, f x ⊆ K)
    (h : ∀ x : ℕ → α, Tendsto x atTop (𝓝 x₀) →
      ∀ y : ℕ → β, (∀ n, y n ∈ f (x n)) → ∀ y₀, Tendsto y atTop (𝓝 y₀) → y₀ ∈ f x₀) :
    UpperHemicontinuousAt f x₀ := by
  refine .of_frequently fun t ht hft ↦ ?_
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hft
  choose y hy using hfx
  obtain ⟨y₀, hy₀, φ, hφ, hyφ⟩ := hK.subseq_of_frequently_in (x := y) <| by
    refine Eventually.frequently ?_
    filter_upwards [hx hf] with n hn
    exact hn (hy n).1
  specialize h (x ∘ φ) (hx.comp hφ.tendsto_atTop) (y ∘ φ) (fun n ↦ (hy _).1) _ hyφ
  exact ⟨y₀, h, ht.closure_eq ▸ mem_closure_of_tendsto hyφ <| .of_forall fun n ↦ (hy _).2⟩

/-- **Sequential characterization of upper hemicontinuity**:
If `β` is a regular space and `f : α → Set β` is upper hemicontinuous at `x₀` and `f x₀` is
closed, then for any sequences `x` and `y` (in `α` and `β`, respectively) tending to `x₀` and `y₀`,
respectively, if `y n ∈ f (x n)` frequently, then `y₀ ∈ f x₀`.

This is a partial converse of `UpperHemicontinuousAt.of_sequences`. -/
lemma UpperHemicontinuousAt.mem_of_tendsto {α β ι : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [RegularSpace β] {f : α → Set β} {x₀ : α} {l : Filter ι}
    (hf : UpperHemicontinuousAt f x₀) (hf_closed : IsClosed (f x₀))
    {x : ι → α} (hx : Tendsto x l (𝓝 x₀))
    {y : ι → β} (hy : ∃ᶠ n in l, y n ∈ f (x n)) {y₀ : β} (hy₀ : Tendsto y l (𝓝 y₀)) :
    y₀ ∈ f x₀ := by
  by_contra
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.disjoint_iff.mp <| RegularSpace.regular hf_closed this
  suffices ∃ᶠ n in l, y n ∈ s by
    apply this
    filter_upwards [hy₀ ht] with n hn hyn
    exact hst.notMem_of_mem_left hyn hn
  apply hy.mp
  filter_upwards [hx (hf s hs)] with n hn hyn
  simp only [← subset_interior_iff_mem_nhdsSet, preimage_setOf_eq, mem_setOf_eq] at hn
  exact interior_subset <| hn hyn
