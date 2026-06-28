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
public import Mathlib.Topology.UniformSpace.Closeds
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Convex.Gauge

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/

public section

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α]
variable {f g : α → Set β} {s : Set α} {x : α}

section facts

variable [TopologicalSpace β]

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

lemma lowerHemicontinuous_iff_isOpen_inter_nonempty :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen {x | (f x ∩ u).Nonempty} := by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_setOf, Filter.Eventually]

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends open sets to open sets. -/
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic uᶜ))ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simpa [this] using lowerHemicontinuous_iff_isOpen_inter_nonempty

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

section singleton_maps

/-! ### Singleton maps

Functions `f : α → β` are continuous if and only if they are lower hemicontinuous if and only if
they are upper hemicontinuous. This is in the sense that the map `g : α → Set β` given by
`g x = {f x}` is both lower or upper hemicontinuous.

This section also provides dot notation to access this fact for continuous functions.
-/

variable {f : α → β} {s : Set α} {x : α}

lemma upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α → Set α) := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]
lemma upperHemicontinuousWithinAt_singleton_iff :
    UpperHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf ↦ upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _ |>.comp hf
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exact mem_of_mem_nhds

@[simp]
lemma upperHemicontinuousAt_singleton_iff :
    UpperHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

@[simp]
lemma upperHemicontinuousOn_singleton_iff :
    UpperHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
  forall₂_congr <| fun _ _ ↦ upperHemicontinuousWithinAt_singleton_iff

@[simp]
lemma upperHemicontinuous_singleton_iff :
    UpperHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← upperHemicontinuousOn_univ_iff]

lemma lowerHemicontinuous_singleton_id : LowerHemicontinuous ({·} : α → Set α) := by
  intro x t ⟨ht, hne⟩
  filter_upwards [ht.mem_nhds (Set.singleton_inter_nonempty.mp hne)] with x' hx'
  exact ⟨ht, Set.singleton_inter_nonempty.mpr hx'⟩

@[simp]
lemma lowerHemicontinuousWithinAt_singleton_iff :
    LowerHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf ↦ (lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt _ _).comp
    hf (mapsTo_image _ _)⟩
  simp only [lowerHemicontinuousWithinAt_iff, Set.singleton_inter_nonempty,
    ContinuousWithinAt, tendsto_iff_forall_eventually_mem]
  intro h t ht
  obtain ⟨u, hut, huo, hux⟩ := mem_nhds_iff.mp ht
  exact (h u huo hux).mono fun _ hx' ↦ hut hx'

@[simp]
lemma lowerHemicontinuousAt_singleton_iff : LowerHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← lowerHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

@[simp]
lemma lowerHemicontinuousOn_singleton_iff : LowerHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
  forall₂_congr <| fun _ _ ↦ lowerHemicontinuousWithinAt_singleton_iff

@[simp]
lemma lowerHemicontinuous_singleton_iff : LowerHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← lowerHemicontinuousOn_univ_iff]

lemma ContinuousWithinAt.upperHemicontinuousWithinAt (hf : ContinuousWithinAt f s x) :
    UpperHemicontinuousWithinAt ({f ·}) s x :=
  upperHemicontinuousWithinAt_singleton_iff.mpr hf

lemma ContinuousWithinAt.lowerHemicontinuousWithinAt (hf : ContinuousWithinAt f s x) :
    LowerHemicontinuousWithinAt ({f ·}) s x :=
  lowerHemicontinuousWithinAt_singleton_iff.mpr hf

lemma ContinuousAt.upperHemicontinuousAt (hf : ContinuousAt f x) :
    UpperHemicontinuousAt ({f ·}) x :=
  upperHemicontinuousAt_singleton_iff.mpr hf

lemma ContinuousAt.lowerHemicontinuousAt (hf : ContinuousAt f x) :
    LowerHemicontinuousAt ({f ·}) x :=
  lowerHemicontinuousAt_singleton_iff.mpr hf

lemma ContinuousOn.upperHemicontinuousOn (hf : ContinuousOn f s) :
    UpperHemicontinuousOn ({f ·}) s :=
  upperHemicontinuousOn_singleton_iff.mpr hf

lemma ContinuousOn.lowerHemicontinuousOn (hf : ContinuousOn f s) :
    LowerHemicontinuousOn ({f ·}) s :=
  lowerHemicontinuousOn_singleton_iff.mpr hf

lemma Continuous.upperHemicontinuous (hf : Continuous f) : UpperHemicontinuous ({f ·}) :=
  upperHemicontinuous_singleton_iff.mpr hf

lemma Continuous.lowerHemicontinuous (hf : Continuous f) : LowerHemicontinuous ({f ·}) :=
  lowerHemicontinuous_singleton_iff.mpr hf

end singleton_maps

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
lemma UpperHemicontinuous.isClosed_domain (hf : UpperHemicontinuous f) :
    IsClosed {x | (f x).Nonempty} := by
  simp only [← isOpen_compl_iff, compl_setOf, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using! hf x ∅

/-! ### Sequential characterizations -/

/-- **Sequential characterization of upper hemicontinuity**:
A set-valued function `f : α → Set β` is upper hemicontinuous at `x₀ : α` if for every pair
of sequences `x : ℕ → α` and `y : ℕ → β` such that `x` tends to `x₀` and `y n ∈ f (x n)` and
`y` tends to `y₀ : β`, then `y₀ ∈ f x₀`. This requires that there is some (sequentially) compact
set containing all `f x'` for `x'` sufficiently close to `x`.

This is a partial converse of `UpperHemicontinuousAt.mem_of_tendsto`. -/
lemma UpperHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
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
lemma UpperHemicontinuousAt.mem_of_tendsto {ι : Type*} [RegularSpace β] {x₀ : α}
    {l : Filter ι} (hf : UpperHemicontinuousAt f x₀) (hf_closed : IsClosed (f x₀))
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

/-- **Sequential characterization of lower hemicontinuity**:
A set-valued function `f : α → Set β` is lower hemicontinuous at `x₀ : α` if for every sequence
`x : ℕ → α` tending to `x₀` and every `y₀ ∈ f x₀`, there exists a sequence `y : ℕ → β` with
`y n ∈ f (x n)` for all `n` that tends to `y₀`. -/
lemma LowerHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    (h : ∀ x : ℕ → α, Tendsto x atTop (𝓝 x₀) →
      ∀ y₀ ∈ f x₀, ∃ y : ℕ → β, (∀ n, y n ∈ f (x n)) ∧ Tendsto y atTop (𝓝 y₀)) :
    LowerHemicontinuousAt f x₀ := by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨y₀, hy₀f, hy₀U⟩
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨x, hx, hxU⟩ := exists_seq_forall_of_frequently hc
  obtain ⟨y, hy_mem, hy_lim⟩ := h x hx y₀ hy₀f
  obtain ⟨n, hn⟩ := (hy_lim.eventually (hU.mem_nhds hy₀U)).exists
  exact hxU n ⟨y n, hy_mem n, hn⟩

end facts

/-! ### Open lower sections -/

/-- A correspondence `f : α → Set β` has open lower sections if and only if its *lower inverse*
(i.e., `b : β ↦ (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b ∈ f x}`) sends every point to an open set. -/
lemma hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl :
    HasOpenLowerSections f ↔ ∀ b, IsOpen (f ⁻¹' (Iic {b}ᶜ))ᶜ := by
  have h (b : β) : (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b ∈ f x} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff]
  simp_rw [h, hasOpenLowerSections_iff_isOpen]

/-- A correspondence `f : α → Set β` has open lower sections if and only if its *upper inverse*
(i.e., `b : β ↦ f ⁻¹' (Iic {b}ᶜ) = {x | b ∉ f x}`) sends every point to a closed set. -/
lemma hasOpenLowerSections_iff_isClosed_preimage_Iic :
    HasOpenLowerSections f ↔ ∀ b, IsClosed (f ⁻¹' (Iic {b}ᶜ)) := by
  simp_rw [← isOpen_compl_iff]
  exact hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl

/-! ### Uniform Limits

Like continuity, hemicontinuity is preserved under certain uniform limits, where the uniformity on
the target `Set β` is the Hausdorff uniformity. In this section, we prove this result for both
lower hemicontinuous and upper hemicontinuous limits.
-/

section limits

variable {ι : Type*} {F : ι → α → Set β} {l : Filter ι} [NeBot l] [UniformSpace β]
open UniformSpace
attribute [local instance] UniformSpace.hausdorff

/-- A net of lower hemicontinuous set-valued functions converging uniformly on `s` (along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit on `s` -/
theorem TendstoUniformlyOn.lowerHemicontinuousOn
    (htendsto : TendstoUniformlyOn F f l s) (hF : ∀ n, LowerHemicontinuousOn (F n) s) :
    LowerHemicontinuousOn f s := by
  rw [lowerHemicontinuousOn_iff]
  intro x₀ hx₀s
  rw [lowerHemicontinuousWithinAt_iff]
  intro V hV ⟨y₀, hy₀f, hy₀V⟩
  -- Obtain entourages W, U ∈ 𝓤 β with U ○ U ○ U ⊆ W
  obtain ⟨W, hW, hWsub⟩ := UniformSpace.mem_nhds_iff.mp (hV.mem_nhds hy₀V)
  obtain ⟨U₁, hU₁, hU₁sym, hU₁comp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U, hU, hUsym, hUcomp⟩ := comp_symm_mem_uniformity_sets hU₁
  have hU_le_U₁ : U ⊆ U₁ := fun _p hp => hUcomp ⟨_, refl_mem_uniformity hU, hp⟩
  -- Eventually, ⟨f x, F N x⟩ ∈ hausdorffEntourage U for all x ∈ s
  have hHU : hausdorffEntourage U ∈ @uniformity (Set β) (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U, hU, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U) hHU).exists
  -- In which case, ⟨y₀, z₀⟩ ∈ U for some z₀ ∈ F N x₀
  obtain ⟨z₀, hz₀FN, hz₀y₀⟩ :=
    ((mem_hausdorffEntourage U (f x₀) (F N x₀)).mp (hN x₀ hx₀s)).1 hy₀f
  -- By lower hemicontinuity, a ball around z₀ intersects all x in a neighborhood of x₀
  obtain ⟨U', ⟨hU'mem, hU'open⟩, hU'sub⟩ := uniformity_hasBasis_open.mem_iff.mp hU
  have hmeet₀ : (F N x₀ ∩ ball z₀ U').Nonempty := ⟨z₀, hz₀FN, mem_ball_self z₀ hU'mem⟩
  have hSmeet : ∀ᶠ x in 𝓝[s] x₀, (F N x ∩ ball z₀ U').Nonempty :=
    lowerHemicontinuousWithinAt_iff.mp (hF _ _ hx₀s) _ (isOpen_ball _ hU'open) hmeet₀
  filter_upwards [hSmeet, self_mem_nhdsWithin] with x ⟨w, hwFN, hwball⟩ hx_s
  obtain ⟨v, hvf, hvw⟩ := ((mem_hausdorffEntourage U (f x) (F N x)).mp (hN x hx_s)).2 hwFN
  exact ⟨v, hvf, hWsub <| hU₁comp
    ⟨w, hUcomp ⟨z₀, hz₀y₀, hU'sub hwball⟩, hU_le_U₁ (hUsym.symm _ _ hvw)⟩⟩

/-- A net of upper hemicontinuous compact-valued set-valued functions converging uniformly on `s`
(along a filter `l`) in the Hausdorff uniformity has an upper hemicontinuous limit on `s` -/
theorem TendstoUniformlyOn.upperHemicontinuousOn
    (htendsto : TendstoUniformlyOn F f l s) (hF : ∀ n, UpperHemicontinuousOn (F n) s)
    (hf_compact : ∀ x ∈ s, IsCompact (f x)) : UpperHemicontinuousOn f s := by
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀s u hu hx₀u
  obtain ⟨W, hW, _, hWu⟩ := lebesgue_number_of_compact_open (hf_compact x₀ hx₀s) hu hx₀u
  obtain ⟨V₁, hV₁, hV₁sym, hV₁comp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U', ⟨hU'mem, hU'open⟩, hU'sub⟩ := uniformity_hasBasis_open.mem_iff.mp hV₁
  have hHU' : hausdorffEntourage U' ∈ @uniformity _ (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U', hU'mem, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U') hHU').exists
  have hFN_image := ((mem_hausdorffEntourage U' (f x₀) (F N x₀)).mp (hN x₀ hx₀s)).2
  simp_rw [upperHemicontinuousOn_iff] at hF
  have hFN_uhc : ∀ᶠ x in 𝓝[s] x₀, F N x ⊆ U'.image (f x₀) :=
    (hF N x₀ hx₀s).forall_isOpen _ hU'open.relImage hFN_image
  filter_upwards [hFN_uhc, self_mem_nhdsWithin] with x hFNx hx_s
  intro y hy
  obtain ⟨z, hzFN, hyz⟩ := ((mem_hausdorffEntourage U' (f x) (F N x)).mp (hN x hx_s)).1 hy
  obtain ⟨y₀, hy₀f, hy₀z⟩ := hFNx hzFN
  exact hWu y₀ hy₀f (hV₁comp ⟨z, hU'sub hy₀z, hV₁sym.symm _ _ (hU'sub hyz)⟩)

/-- A net of lower hemicontinuous set-valued functions converging uniformly (along a
filter `l`) in the Hausdorff uniformity has a lower hemicontinuous limit -/
theorem TendstoUniformly.lowerHemicontinuous
    (htendsto : TendstoUniformly F f l) (hF : ∀ n, LowerHemicontinuous (F n)) :
    LowerHemicontinuous f := by
  rw [← lowerHemicontinuousOn_univ_iff]
  exact (@htendsto.tendstoUniformlyOn _ _ _ (UniformSpace.hausdorff (α := β)) F f Set.univ l)
    |>.lowerHemicontinuousOn (fun n ↦ (hF n).lowerHemicontinuousOn _)

/-- A net of upper hemicontinuous compact-valued set-valued functions converging uniformly
(along a filter `l`) in the Hausdorff uniformity has an upper hemicontinuous limit -/
theorem TendstoUniformly.upperHemicontinuous
    (htendsto : TendstoUniformly F f l) (hF : ∀ n, UpperHemicontinuous (F n))
    (hf_compact : ∀ x, IsCompact (f x)) : UpperHemicontinuous f := by
  rw [← upperHemicontinuousOn_univ_iff]
  exact (@htendsto.tendstoUniformlyOn _ _ _ (UniformSpace.hausdorff (α := β)) F f Set.univ l)
    |>.upperHemicontinuousOn (fun n ↦ (hF n).upperHemicontinuousOn _) (fun x _ ↦ hf_compact x)

end limits

section intersections

/-! ### Special Intersections -/

/-- A lower hemicontinuous correspondence intersected with a correspondence with an open graph is
lower hemicontinuous. -/
lemma LowerHemicontinuous.inter_hasOpenCGraph [TopologicalSpace β] (hf : LowerHemicontinuous f)
    (hg : HasOpenCGraph g) : LowerHemicontinuous (fun x ↦ f x ∩ g x) := by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg) x y hyg
  refine ⟨U ∩ {x' | (f x' ∩ (t ∩ V)).Nonempty}, ?_, hU.inter (hf _ (ht.inter hV)),
      ⟨hxU, y, hyf, hyt, hyV⟩⟩
  intro x' ⟨hx'U, z, hzf, hzt, hzV⟩
  exact ⟨z, ⟨hzf, hUV (Set.mk_mem_prod hx'U hzV)⟩, hzt⟩

variable [AddCommGroup β] [Module ℝ β] [UniformSpace β] [IsUniformAddGroup β]
  [ContinuousSMul ℝ β] {K : Set β}

attribute [local instance] UniformSpace.hausdorff

/-- A lower hemicontinuous correspondence with star convex values about 0 intersected with an
absolutely convex, compact neighborhood of zero is lower hemicontinuous. -/
lemma LowerHemicontinuous.inter_isCompact_absConvex
    (hf : LowerHemicontinuous f) (hK_compact : IsCompact K) (hK_convex : AbsConvex ℝ K)
    (hK_nhd : K ∈ 𝓝 0) (hf_star : ∀ x, StarConvex ℝ 0 (f x)) :
    LowerHemicontinuous (fun x ↦ f x ∩ K) := by
  suffices TendstoUniformly (fun ε x ↦ f x ∩ {y | gauge K y < ε}) (fun x ↦ f x ∩ K) (𝓝[>] 1) by
    exact this.lowerHemicontinuous fun _ ↦ hf.inter_hasOpenCGraph
      (HasOpenCGraph.const (setOf_gauge_lt_isOpen hK_convex.convex hK_nhd _))
  intro V hV
  obtain ⟨U_base, hU_base, hU_sub⟩ := (mem_lift'_sets monotone_hausdorffEntourage).mp hV
  obtain ⟨W, hW, hW_sub⟩ := (𝓝 (0 : β)).basis_sets.uniformity_of_nhds_zero.mem_iff.mp hU_base
  have h_smul : ∀ᶠ t : ℝ in 𝓝 0, ∀ k ∈ K, t • k ∈ W :=
    hK_compact.eventually_forall_of_forall_eventually fun k _ =>
      (continuous_fst.smul continuous_snd).tendsto ((0 : ℝ), k) |>.eventually
        (by simpa [zero_smul] using hW)
  have h_tend : Tendsto (fun ε : ℝ => ε - 1) (𝓝[>] 1) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε - 1) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  filter_upwards [h_tend.eventually h_smul, self_mem_nhdsWithin] with ε h_eps hε_gt x
  apply hU_sub
  apply monotone_hausdorffEntourage hW_sub
  have hε_pos : (0 : ℝ) < ε := one_pos.trans hε_gt
  refine ⟨?_, ?_⟩
  · intro c ⟨hcf, hcK⟩
    refine ⟨c, ⟨hcf, ?_⟩, by simp [mem_of_mem_nhds hW]⟩
    grw [mem_setOf, gauge_le_one_of_mem hcK]
    exact hε_gt
  · intro b ⟨hbf, hbKs⟩
    have h_c : (1 / ε) • b ∈ K := hK_convex.convex.inv_smul_mem (mem_of_mem_nhds hK_nhd)
        (absorbent_nhds_zero hK_nhd) hbKs (by positivity)
    refine ⟨(1 / ε) • b, ⟨?_, h_c⟩, ?_⟩
    · rw [← mem_inv_smul_set_iff₀ (by positivity)]
      exact (hf_star x).mem_smul hbf (by grind)
    · simp only [Set.mem_setOf_eq, id]
      rw [show b - (1 / ε) • b = (ε - 1) • ((1 / ε) • b) by
        rw [smul_smul, show (ε - 1) * (1 / ε) = 1 - 1 / ε by
          field_simp, sub_smul, one_smul]]
      exact h_eps _ h_c

end intersections
