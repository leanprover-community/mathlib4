/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.NhdsWithin

/-!
# Neighborhoods and continuity relative to a subset

This file develops API on the relative versions

* `ContinuousOn`        of `Continuous`
* `ContinuousWithinAt`  of `ContinuousAt`

related to continuity, which are defined in previous definition files.
Their basic properties studied in this file include the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

-/

public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ] {f g : α → β} {s s' s₁ t : Set α} {x : α}

/-!
## `ContinuousWithinAt`
-/

/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `Filter.Tendsto.comp` as
`ContinuousWithinAt.comp` will have a different meaning. -/
theorem ContinuousWithinAt.tendsto (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝 (f x)) :=
  h

theorem continuousWithinAt_univ (f : α → β) (x : α) :
    ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt, ContinuousWithinAt, nhdsWithin_univ]

@[simp]
theorem continuousOn_univ {f : α → β} : ContinuousOn f univ ↔ Continuous f := by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]

theorem continuousWithinAt_iff_continuousAt_restrict (f : α → β) {x : α} {s : Set α} (h : x ∈ s) :
    ContinuousWithinAt f s x ↔ ContinuousAt (s.restrict f) ⟨x, h⟩ :=
  tendsto_nhdsWithin_iff_subtype h f _

theorem ContinuousWithinAt.tendsto_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) :
    Tendsto f (𝓝[s] x) (𝓝[t] f x) :=
  tendsto_inf.2 ⟨h, tendsto_principal.2 <| mem_inf_of_right <| mem_principal.2 <| ht⟩

theorem ContinuousWithinAt.tendsto_nhdsWithin_image (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝[f '' s] f x) :=
  h.tendsto_nhdsWithin (mapsTo_image _ _)

theorem nhdsWithin_le_comap (ctsf : ContinuousWithinAt f s x) :
    𝓝[s] x ≤ comap f (𝓝[f '' s] f x) :=
  ctsf.tendsto_nhdsWithin_image.le_comap

theorem ContinuousWithinAt.preimage_mem_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝[s] x :=
  h ht

theorem ContinuousWithinAt.preimage_mem_nhdsWithin' {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝[f '' s] f x) : f ⁻¹' t ∈ 𝓝[s] x :=
  h.tendsto_nhdsWithin (mapsTo_image _ _) ht

theorem ContinuousWithinAt.preimage_mem_nhdsWithin'' {y : β} {s t : Set β}
    (h : ContinuousWithinAt f (f ⁻¹' s) x) (ht : t ∈ 𝓝[s] y) (hxy : y = f x) :
    f ⁻¹' t ∈ 𝓝[f ⁻¹' s] x := by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)

theorem continuousWithinAt_of_notMem_closure (hx : x ∉ closure s) :
    ContinuousWithinAt f s x := by
  rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
  rw [ContinuousWithinAt, hx]
  exact tendsto_bot

/-!
## `ContinuousOn`
-/

theorem continuousOn_iff :
    ContinuousOn f s ↔
      ∀ x ∈ s, ∀ t : Set β, IsOpen t → f x ∈ t → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' t := by
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]

theorem ContinuousOn.continuousWithinAt (hf : ContinuousOn f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  hf x hx

theorem continuousOn_iff_continuous_restrict :
    ContinuousOn f s ↔ Continuous (s.restrict f) := by
  rw [ContinuousOn, continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_restrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_restrict f xs).mpr (h ⟨x, xs⟩)

alias ⟨ContinuousOn.restrict, _⟩ := continuousOn_iff_continuous_restrict

theorem ContinuousOn.mapsToRestrict {t : Set β} (hf : ContinuousOn f s) (ht : MapsTo f s t) :
    Continuous (ht.restrict f s t) :=
  hf.restrict.codRestrict _

@[deprecated (since := "2025-09-05")]
alias ContinuousOn.restrict_mapsTo := ContinuousOn.mapsToRestrict

theorem continuousOn_iff' :
    ContinuousOn f s ↔ ∀ t : Set β, IsOpen t → ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsOpen (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isOpen_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, by simpa only [Set.inter_comm, eq_comm] using useq⟩
  rw [continuousOn_iff_continuous_restrict, continuous_def]; simp only [this]

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any finer topology on the source space. -/
theorem ContinuousOn.mono_dom {α β : Type*} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₁) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₃ f s) :
    @ContinuousOn α β t₂ t₃ f s := fun x hx _u hu =>
  map_mono (inf_le_inf_right _ <| nhds_mono h₁) (h₂ x hx hu)

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any coarser topology on the target space. -/
theorem ContinuousOn.mono_rng {α β : Type*} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₃) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₂ f s) :
    @ContinuousOn α β t₁ t₃ f s := fun x hx _u hu =>
  h₂ x hx <| nhds_mono h₁ hu

theorem continuousOn_iff_isClosed :
    ContinuousOn f s ↔ ∀ t : Set β, IsClosed t → ∃ u, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsClosed (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isClosed_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm, Set.inter_comm s]
  rw [continuousOn_iff_continuous_restrict, continuous_iff_isClosed]; simp only [this]

theorem continuous_of_cover_nhds {ι : Sort*} {s : ι → Set α}
    (hs : ∀ x : α, ∃ i, s i ∈ 𝓝 x) (hf : ∀ i, ContinuousOn f (s i)) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x ↦ let ⟨i, hi⟩ := hs x; by
    rw [ContinuousAt, ← nhdsWithin_eq_nhds.2 hi]
    exact hf _ _ (mem_of_mem_nhds hi)

@[simp] theorem continuousOn_empty (f : α → β) : ContinuousOn f ∅ := fun _ => False.elim

@[simp]
theorem continuousOn_singleton (f : α → β) (a : α) : ContinuousOn f {a} :=
  forall_eq.2 <| by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds

theorem Set.Subsingleton.continuousOn {s : Set α} (hs : s.Subsingleton) (f : α → β) :
    ContinuousOn f s :=
  hs.induction_on (continuousOn_empty f) (continuousOn_singleton f)

theorem continuousOn_open_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ t, IsOpen t → IsOpen (s ∩ f ⁻¹' t) := by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm, hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine ⟨s ∩ f ⁻¹' t, h t ht, ?_⟩
    rw [@inter_comm _ s (f ⁻¹' t), inter_assoc, inter_self]

theorem ContinuousOn.isOpen_inter_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ f ⁻¹' t) :=
  (continuousOn_open_iff hs).1 hf t ht

theorem ContinuousOn.isOpen_preimage {t : Set β} (h : ContinuousOn f s)
    (hs : IsOpen s) (hp : f ⁻¹' t ⊆ s) (ht : IsOpen t) : IsOpen (f ⁻¹' t) := by
  convert (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm, inter_eq_self_of_subset_left hp]

theorem ContinuousOn.preimage_isClosed_of_isClosed {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ f ⁻¹' t) := by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm, hu.2]
  apply IsClosed.inter hu.1 hs

theorem ContinuousOn.preimage_interior_subset_interior_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) : s ∩ f ⁻¹' interior t ⊆ s ∩ interior (f ⁻¹' t) :=
  calc
    s ∩ f ⁻¹' interior t ⊆ interior (s ∩ f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.isOpen_inter_preimage hs isOpen_interior)
    _ = s ∩ interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]

theorem continuousOn_of_locally_continuousOn
    (h : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ContinuousOn f (s ∩ t)) : ContinuousOn f s := by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this

theorem continuousOn_to_generateFrom_iff {β : Type*} {T : Set (Set β)} {f : α → β} :
    @ContinuousOn α β _ (.generateFrom T) f s ↔ ∀ x ∈ s, ∀ t ∈ T, f x ∈ t → f ⁻¹' t ∈ 𝓝[s] x :=
  forall₂_congr fun x _ => by
    delta ContinuousWithinAt
    simp only [TopologicalSpace.nhds_generateFrom, tendsto_iInf, tendsto_principal, mem_setOf_eq,
      and_imp]
    exact forall_congr' fun t => forall_swap

theorem continuousOn_isOpen_of_generateFrom {β : Type*} {s : Set α} {T : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ T, IsOpen (s ∩ f ⁻¹' t)) :
    @ContinuousOn α β _ (.generateFrom T) f s :=
  continuousOn_to_generateFrom_iff.2 fun _x hx t ht hxt => mem_nhdsWithin.2
    ⟨_, h t ht, ⟨hx, hxt⟩, fun _y hy => hy.1.2⟩

/-!
## Congruence and monotonicity properties with respect to sets
-/

theorem ContinuousWithinAt.mono (h : ContinuousWithinAt f t x)
    (hs : s ⊆ t) : ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_mono x hs)

theorem ContinuousWithinAt.mono_of_mem_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_le_of_mem hs)

/-- If two sets coincide around `x`, then being continuous within one or the other at `x` is
equivalent. See also `continuousWithinAt_congr_set'` which requires that the sets coincide
locally away from a point `y`, in a T1 space. -/
theorem continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq.mpr h]

theorem ContinuousWithinAt.congr_set (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f t x :=
  (continuousWithinAt_congr_set h).1 hf

theorem continuousWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]

theorem continuousWithinAt_inter (h : t ∈ 𝓝 x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]

theorem continuousWithinAt_union :
    ContinuousWithinAt f (s ∪ t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]

theorem ContinuousWithinAt.union (hs : ContinuousWithinAt f s x) (ht : ContinuousWithinAt f t x) :
    ContinuousWithinAt f (s ∪ t) x :=
  continuousWithinAt_union.2 ⟨hs, ht⟩

@[simp]
theorem continuousWithinAt_singleton : ContinuousWithinAt f {x} x := by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]

@[simp]
theorem continuousWithinAt_insert_self :
    ContinuousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x := by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton, true_and]

protected alias ⟨_, ContinuousWithinAt.insert⟩ := continuousWithinAt_insert_self

/- `continuousWithinAt_insert` gives the same equivalence but at a point `y` possibly different
from `x`. As this requires the space to be T1, and this property is not available in this file,
this is found in another file although it is part of the basic API for `continuousWithinAt`. -/

theorem ContinuousWithinAt.diff_iff
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x :=
  ⟨fun h => (h.union ht).mono <| by simp only [diff_union_self, subset_union_left], fun h =>
    h.mono diff_subset⟩

/-- See also `continuousWithinAt_diff_singleton` for the case of `s \ {y}`, but
requiring `T1Space α`. -/
@[simp]
theorem continuousWithinAt_diff_self :
    ContinuousWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_singleton.diff_iff

/-- A function is continuous at a point `x` within a set `s` if `x` is not an accumulation point of
`s`. -/
lemma continuousWithinAt_of_not_accPt (h : ¬AccPt x (𝓟 s)) : ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_diff_self]
  simp_all [ContinuousWithinAt, AccPt, ← nhdsWithin_inter', Set.diff_eq, Set.inter_comm]

@[simp]
theorem continuousWithinAt_compl_self :
    ContinuousWithinAt f {x}ᶜ x ↔ ContinuousAt f x := by
  rw [compl_eq_univ_diff, continuousWithinAt_diff_self, continuousWithinAt_univ]

/-- A function is continuous at a point `x` if `x` is isolated. -/
lemma continuousAt_of_not_accPt (h : ¬AccPt x (𝓟 {x}ᶜ)) : ContinuousAt f x := by
  rw [← continuousWithinAt_compl_self]
  exact continuousWithinAt_of_not_accPt h

/-- A function is continuous at a point `x` if `x` is isolated. -/
lemma continuousAt_of_not_accPt_top (h : ¬AccPt x ⊤) : ContinuousAt f x :=
  continuousAt_of_not_accPt fun hh ↦ h <| AccPt.mono hh (by simp)

theorem ContinuousOn.mono (hf : ContinuousOn f s) (h : t ⊆ s) :
    ContinuousOn f t := fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)

theorem antitone_continuousOn {f : α → β} : Antitone (ContinuousOn f) := fun _s _t hst hf =>
  hf.mono hst

/-!
## Relation between `ContinuousAt` and `ContinuousWithinAt`
-/

@[fun_prop]
theorem ContinuousAt.continuousWithinAt (h : ContinuousAt f x) :
    ContinuousWithinAt f s x :=
  ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)

theorem continuousWithinAt_iff_continuousAt (h : s ∈ 𝓝 x) :
    ContinuousWithinAt f s x ↔ ContinuousAt f x := by
  rw [← univ_inter s, continuousWithinAt_inter h, continuousWithinAt_univ]

theorem ContinuousWithinAt.continuousAt
    (h : ContinuousWithinAt f s x) (hs : s ∈ 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp h

theorem IsOpen.continuousOn_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ ⦃a⦄, a ∈ s → ContinuousAt f a :=
  forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds

theorem ContinuousOn.continuousAt (h : ContinuousOn f s)
    (hx : s ∈ 𝓝 x) : ContinuousAt f x :=
  (h x (mem_of_mem_nhds hx)).continuousAt hx

theorem continuousOn_of_forall_continuousAt (hcont : ∀ x ∈ s, ContinuousAt f x) :
    ContinuousOn f s := fun x hx => (hcont x hx).continuousWithinAt

@[fun_prop]
theorem Continuous.continuousOn (h : Continuous f) : ContinuousOn f s := by
  rw [← continuousOn_univ] at h
  exact h.mono (subset_univ _)

@[fun_prop]
theorem Continuous.continuousWithinAt (h : Continuous f) :
    ContinuousWithinAt f s x :=
  h.continuousAt.continuousWithinAt


/-!
## Congruence properties with respect to functions
-/

theorem ContinuousOn.congr_mono (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) :
    ContinuousOn g s₁ := by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventuallyEq_nhdsWithin.symm

theorem ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn g f s) :
    ContinuousOn g s :=
  h.congr_mono h' (Subset.refl _)

theorem continuousOn_congr (h' : EqOn g f s) :
    ContinuousOn g s ↔ ContinuousOn f s :=
  ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩

theorem Filter.EventuallyEq.congr_continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x := by
  rw [ContinuousWithinAt, hx, tendsto_congr' h, ContinuousWithinAt]

theorem ContinuousWithinAt.congr_of_eventuallyEq
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    ContinuousWithinAt g s x :=
  (h₁.congr_continuousWithinAt hx).2 h

theorem ContinuousWithinAt.congr_of_eventuallyEq_of_mem
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

theorem Filter.EventuallyEq.congr_continuousWithinAt_of_mem (h : f =ᶠ[𝓝[s] x] g) (hx : x ∈ s) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_of_mem h.symm hx,
    fun h' ↦  h'.congr_of_eventuallyEq_of_mem h hx⟩

theorem ContinuousWithinAt.congr_of_eventuallyEq_insert
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[insert x s] x] f) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)
    (mem_of_mem_nhdsWithin (mem_insert _ _) h₁ :)

theorem Filter.EventuallyEq.congr_continuousWithinAt_of_insert (h : f =ᶠ[𝓝[insert x s] x] g) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_insert h.symm,
    fun h' ↦  h'.congr_of_eventuallyEq_insert h⟩

theorem ContinuousWithinAt.congr (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ s, g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx

theorem continuousWithinAt_congr (h₁ : ∀ y ∈ s, g y = f y) (hx : g x = f x) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  ⟨fun h' ↦ h'.congr (fun x hx ↦ (h₁ x hx).symm) hx.symm, fun h' ↦  h'.congr h₁ hx⟩

theorem ContinuousWithinAt.congr_of_mem (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ s, g y = f y) (hx : x ∈ s) : ContinuousWithinAt g s x :=
  h.congr h₁ (h₁ x hx)

theorem continuousWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, g y = f y) (hx : x ∈ s) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr h₁ (h₁ x hx)

theorem ContinuousWithinAt.congr_of_insert (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ insert x s, g y = f y) : ContinuousWithinAt g s x :=
  h.congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

theorem continuousWithinAt_congr_of_insert
    (h₁ : ∀ y ∈ insert x s, g y = f y) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

theorem ContinuousWithinAt.congr_mono
    (h : ContinuousWithinAt f s x) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) (hx : g x = f x) :
    ContinuousWithinAt g s₁ x :=
  (h.mono h₁).congr h' hx

theorem ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) :
    ContinuousAt g x :=
  congr h (EventuallyEq.symm hg)

/-!
## Composition
-/

theorem ContinuousWithinAt.comp {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (hf.tendsto_nhdsWithin h)

theorem ContinuousWithinAt.comp' {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (fun x => g (f x)) s x :=
  hg.comp hf h

theorem ContinuousWithinAt.comp_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t)
    (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp hf h

theorem ContinuousWithinAt.comp_inter {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

theorem ContinuousWithinAt.comp_inter_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter hf

theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t ∈ 𝓝[s] x) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf h)

theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t ∈ 𝓝[s] x)
    (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin hf h

theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x)
    (hs : t ∈ 𝓝[f '' s] f x) : ContinuousWithinAt (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp hf (mapsTo_image f s)

theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x)
    (hs : t ∈ 𝓝[f '' s] y) (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image hf hs

@[fun_prop] theorem ContinuousAt.comp_continuousWithinAt {g : β → γ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) s x :=
  hg.continuousWithinAt.comp hf (mapsTo_univ _ _)

theorem ContinuousAt.comp_continuousWithinAt_of_eq {g : β → γ} {y : β}
    (hg : ContinuousAt g y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_continuousWithinAt hf

/-- See also `ContinuousOn.comp'` using the form `fun y ↦ g (f y)` instead of `g ∘ f`. -/
theorem ContinuousOn.comp {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s := fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h

/-- Variant of `ContinuousOn.comp` using the form `fun y ↦ g (f y)` instead of `g ∘ f`. -/
@[fun_prop]
theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : Set.MapsTo f s t) : ContinuousOn (fun x => g (f x)) s :=
  ContinuousOn.comp hg hf h

@[fun_prop]
theorem ContinuousOn.comp_inter {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- See also `Continuous.comp_continuousOn'` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`. -/
theorem Continuous.comp_continuousOn {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) s :=
  hg.continuousOn.comp hf (mapsTo_univ _ _)

/-- Variant of `Continuous.comp_continuousOn` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`. -/
@[fun_prop]
theorem Continuous.comp_continuousOn' {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (fun x ↦ g (f x)) s :=
  hg.comp_continuousOn hf

theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
    (hf : Continuous f) (hs : ∀ x, f x ∈ s) : Continuous (g ∘ f) := by
  rw [← continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x

theorem ContinuousOn.image_comp_continuous {g : β → γ} {f : α → β} {s : Set α}
    (hg : ContinuousOn g (f '' s)) (hf : Continuous f) : ContinuousOn (g ∘ f) s :=
  hg.comp hf.continuousOn (s.mapsTo_image f)

theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
    {s : Set α} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousWithinAt g s x)
    (hh : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x :=
  ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)

theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ → δ} {g : α → β}
    {h : α → γ} {x : α} {s : Set α} {y : β × γ} (hf : ContinuousAt f y)
    (hg : ContinuousWithinAt g s x) (hh : ContinuousWithinAt h s x) (e : (g x, h x) = y) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x := by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh

/-!
## Image
-/

theorem ContinuousWithinAt.mem_closure_image
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
  mem_closure_of_tendsto h <| mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)

theorem ContinuousWithinAt.mem_closure {t : Set β}
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) (ht : MapsTo f s t) : f x ∈ closure t :=
  closure_mono (image_subset_iff.2 ht) (h.mem_closure_image hx)

theorem Set.MapsTo.closure_of_continuousWithinAt {t : Set β}
    (h : MapsTo f s t) (hc : ∀ x ∈ closure s, ContinuousWithinAt f s x) :
    MapsTo f (closure s) (closure t) := fun x hx => (hc x hx).mem_closure hx h

theorem Set.MapsTo.closure_of_continuousOn {t : Set β} (h : MapsTo f s t)
    (hc : ContinuousOn f (closure s)) : MapsTo f (closure s) (closure t) :=
  h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure

theorem ContinuousWithinAt.image_closure
    (hf : ∀ x ∈ closure s, ContinuousWithinAt f s x) : f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure_of_continuousWithinAt hf).image_subset

theorem ContinuousOn.image_closure (hf : ContinuousOn f (closure s)) :
    f '' closure s ⊆ closure (f '' s) :=
  ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure

/-!
## Product
-/

theorem ContinuousWithinAt.prodMk {f : α → β} {g : α → γ} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prodMk_nhds hg

@[fun_prop]
theorem ContinuousOn.prodMk {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

theorem continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.continuousOn

theorem continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.continuousWithinAt

@[fun_prop]
theorem ContinuousOn.fst {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuousOn hf

theorem ContinuousWithinAt.fst {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuousAt_fst.comp_continuousWithinAt h

theorem continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.continuousOn

theorem continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.continuousWithinAt

@[fun_prop]
theorem ContinuousOn.snd {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuousOn hf

theorem ContinuousWithinAt.snd {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuousAt_snd.comp_continuousWithinAt h

theorem continuousWithinAt_prod_iff {f : α → β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prodMk h2⟩

theorem ContinuousWithinAt.prodMap {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) :=
  .prodMk (hf.comp continuousWithinAt_fst mapsTo_fst_prod)
    (hg.comp continuousWithinAt_snd mapsTo_snd_prod)

theorem ContinuousOn.prodMap {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) := fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  (hf x hx).prodMap (hg y hy)

theorem continuousWithinAt_prod_of_discrete_left [DiscreteTopology α]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨x.1, ·⟩) {b | (x.1, b) ∈ s} x.2 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl

theorem continuousWithinAt_prod_of_discrete_right [DiscreteTopology β]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨·, x.2⟩) {a | (a, x.2) ∈ s} x.1 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl

theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨x.1, ·⟩) x.2 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left

theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨·, x.2⟩) x.1 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right

theorem continuousOn_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (f ⟨a, ·⟩) {b | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl

theorem continuousOn_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ b, ContinuousOn (f ⟨·, b⟩) {a | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_swap

/-- If a function `f a b` is such that `y ↦ f a b` is continuous for all `a`, and `a` lives in a
discrete space, then `f` is continuous, and vice versa. -/
theorem continuous_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    Continuous f ↔ ∀ a, Continuous (f ⟨a, ·⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_left

theorem continuous_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    Continuous f ↔ ∀ b, Continuous (f ⟨·, b⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_right

theorem isOpenMap_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ a, IsOpenMap (f ⟨a, ·⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl

theorem isOpenMap_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ b, IsOpenMap (f ⟨·, b⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_swap (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl

theorem ContinuousOn.uncurry_left {f : α → β → γ} {sα : Set α} {sβ : Set β} (a : α) (ha : a ∈ sα)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (f a) sβ := by
  let g : β → γ := f.uncurry ∘ (fun b => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

theorem ContinuousOn.uncurry_right {f : α → β → γ} {sα : Set α} {sβ : Set β} (b : β) (ha : b ∈ sβ)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (fun a => f a b) sα := by
  let g : α → γ := f.uncurry ∘ (fun a => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

/-!
## Pi
-/

theorem continuousWithinAt_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds

theorem continuousOn_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} : ContinuousOn f s ↔ ∀ i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]
theorem continuousOn_pi' {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} (hf : ∀ i, ContinuousOn (fun y => f y i) s) :
    ContinuousOn f s :=
  continuousOn_pi.2 hf

@[fun_prop]
theorem continuousOn_apply {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (i : ι) (s) : ContinuousOn (fun p : ∀ i, X i => p i) s :=
  Continuous.continuousOn (continuous_apply i)


/-!
## Specific functions
-/

@[fun_prop]
theorem continuousOn_const {s : Set α} {c : β} : ContinuousOn (fun _ => c) s :=
  continuous_const.continuousOn

@[fun_prop]
theorem continuousWithinAt_const {b : β} {s : Set α} {x : α} :
    ContinuousWithinAt (fun _ : α => b) s x :=
  continuous_const.continuousWithinAt

theorem continuousOn_id {s : Set α} : ContinuousOn id s :=
  continuous_id.continuousOn

@[fun_prop]
theorem continuousOn_id' (s : Set α) : ContinuousOn (fun x : α => x) s := continuousOn_id

theorem continuousWithinAt_id {s : Set α} {x : α} : ContinuousWithinAt id s x :=
  continuous_id.continuousWithinAt

protected theorem ContinuousOn.iterate {f : α → α} {s : Set α} (hcont : ContinuousOn f s)
    (hmaps : MapsTo f s s) : ∀ n, ContinuousOn (f^[n]) s
  | 0 => continuousOn_id
  | (n + 1) => (hcont.iterate hmaps n).comp hcont hmaps

section Fin
variable {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (X i)]

theorem ContinuousWithinAt.finCons
    {f : α → X 0} {g : α → ∀ j : Fin n, X (Fin.succ j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.cons (f a) (g a)) s a :=
  hf.tendsto.finCons hg

theorem ContinuousOn.finCons {f : α → X 0} {s : Set α} {g : α → ∀ j : Fin n, X (Fin.succ j)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.cons (f a) (g a)) s := fun a ha =>
  (hf a ha).finCons (hg a ha)

theorem ContinuousWithinAt.matrixVecCons {f : α → β} {g : α → Fin n → β} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Matrix.vecCons (f a) (g a)) s a :=
  hf.tendsto.matrixVecCons hg

theorem ContinuousOn.matrixVecCons {f : α → β} {g : α → Fin n → β} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Matrix.vecCons (f a) (g a)) s := fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)

theorem ContinuousWithinAt.finSnoc
    {f : α → ∀ j : Fin n, X (Fin.castSucc j)} {g : α → X (Fin.last _)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.snoc (f a) (g a)) s a :=
  hf.tendsto.finSnoc hg

theorem ContinuousOn.finSnoc
    {f : α → ∀ j : Fin n, X (Fin.castSucc j)} {g : α → X (Fin.last _)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.snoc (f a) (g a)) s := fun a ha =>
  (hf a ha).finSnoc (hg a ha)

theorem ContinuousWithinAt.finInsertNth
    (i : Fin (n + 1)) {f : α → X i} {g : α → ∀ j : Fin n, X (i.succAbove j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.tendsto.finInsertNth i hg

theorem ContinuousOn.finInsertNth
    (i : Fin (n + 1)) {f : α → X i} {g : α → ∀ j : Fin n, X (i.succAbove j)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)

end Fin

theorem Set.LeftInvOn.map_nhdsWithin_eq {f : α → β} {g : β → α} {x : β} {s : Set β}
    (h : LeftInvOn f g s) (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s) (g x))
    (hg : ContinuousWithinAt g s x) : map g (𝓝[s] x) = 𝓝[g '' s] g x := by
  apply le_antisymm
  · exact hg.tendsto_nhdsWithin (mapsTo_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.rightInvOn_image.eqOn.eventuallyEq_of_mem self_mem_nhdsWithin
    refine le_map_of_right_inverse A ?_
    simpa only [hx] using hf.tendsto_nhdsWithin (h.mapsTo (surjOn_image _ _))

theorem Function.LeftInverse.map_nhds_eq {f : α → β} {g : β → α} {x : β}
    (h : Function.LeftInverse f g) (hf : ContinuousWithinAt f (range g) (g x))
    (hg : ContinuousAt g x) : map g (𝓝 x) = 𝓝[range g] g x := by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.leftInvOn univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuousWithinAt

lemma Topology.IsInducing.continuousWithinAt_iff {f : α → β} {g : β → γ} (hg : IsInducing g)
    {s : Set α} {x : α} : ContinuousWithinAt f s x ↔ ContinuousWithinAt (g ∘ f) s x := by
  simp_rw [ContinuousWithinAt, hg.tendsto_nhds_iff]; rfl

lemma Topology.IsInducing.continuousOn_iff {f : α → β} {g : β → γ} (hg : IsInducing g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s := by
  simp_rw [ContinuousOn, hg.continuousWithinAt_iff]

lemma Topology.IsInducing.map_nhdsWithin_eq {f : α → β} (hf : IsInducing f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x := by
  ext; simp +contextual [mem_nhdsWithin_iff_eventually, hf.nhds_eq_comap, forall_comm (α := _ ∈ _)]

lemma Topology.IsInducing.continuousOn_image_iff {g : β → γ} {s : Set α} (hf : IsInducing f) :
    ContinuousOn g (f '' s) ↔ ContinuousOn (g ∘ f) s := by
  simp [ContinuousOn, ContinuousWithinAt, ← hf.map_nhdsWithin_eq]

lemma Topology.IsEmbedding.continuousOn_iff {f : α → β} {g : β → γ} (hg : IsEmbedding g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s :=
  hg.isInducing.continuousOn_iff

lemma Topology.IsEmbedding.map_nhdsWithin_eq {f : α → β} (hf : IsEmbedding f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x :=
  hf.isInducing.map_nhdsWithin_eq s x

theorem Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq {f : α → β} (hf : IsOpenEmbedding f)
    (s : Set β) (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x := by
  rw [hf.isEmbedding.map_nhdsWithin_eq, image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.isOpen_range
  rw [inter_assoc, inter_self]

theorem Topology.IsQuotientMap.continuousOn_isOpen_iff {f : α → β} {g : β → γ} (h : IsQuotientMap f)
    {s : Set β} (hs : IsOpen s) : ContinuousOn g s ↔ ContinuousOn (g ∘ f) (f ⁻¹' s) := by
  simp only [continuousOn_iff_continuous_restrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl

theorem IsOpenMap.continuousOn_image_of_leftInvOn {f : α → β} {s : Set α}
    (h : IsOpenMap (s.restrict f)) {finv : β → α} (hleft : LeftInvOn finv f s) :
    ContinuousOn finv (f '' s) := by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t ∩ s), ?_, ?_⟩
  · rw [← image_restrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_mono inter_subset_right), hleft.image_inter']

theorem IsOpenMap.continuousOn_range_of_leftInverse {f : α → β} (hf : IsOpenMap f) {finv : β → α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (range f) := by
  rw [← image_univ]
  exact (hf.restrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x

/-- If `f` is continuous on an open set `s` and continuous at each point of another
set `t` then `f` is continuous on `s ∪ t`. -/
lemma ContinuousOn.union_continuousAt {f : α → β} (s_op : IsOpen s)
    (hs : ContinuousOn f s) (ht : ∀ x ∈ t, ContinuousAt f x) :
    ContinuousOn f (s ∪ t) :=
  continuousOn_of_forall_continuousAt <| fun _ hx => hx.elim
  (fun h => ContinuousWithinAt.continuousAt (continuousWithinAt hs h) <| IsOpen.mem_nhds s_op h)
  (ht _)

open Classical in
/-- If a function is continuous on two closed sets, it is also continuous on their union. -/
theorem ContinuousOn.union_of_isClosed {f : α → β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsClosed s) (ht : IsClosed t) : ContinuousOn f (s ∪ t) := by
  refine fun x hx ↦ .union ?_ ?_
  · refine if hx : x ∈ s then hfs x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if hx : x ∈ t then hft x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

/-- A function is continuous on two closed sets iff it is also continuous on their union. -/
theorem continouousOn_union_iff_of_isClosed {f : α → β} (hs : IsClosed s) (ht : IsClosed t) :
    ContinuousOn f (s ∪ t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h ↦ ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h ↦ h.left.union_of_isClosed h.right hs ht⟩

/-- If a function is continuous on two open sets, it is also continuous on their union. -/
theorem ContinuousOn.union_of_isOpen {f : α → β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsOpen s) (ht : IsOpen t) : ContinuousOn f (s ∪ t) :=
  union_continuousAt hs hfs fun _ hx ↦ ht.continuousOn_iff.mp hft hx

/-- A function is continuous on two open sets iff it is also continuous on their union. -/
theorem continouousOn_union_iff_of_isOpen {f : α → β} (hs : IsOpen s) (ht : IsOpen t) :
    ContinuousOn f (s ∪ t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h ↦ ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h ↦ h.left.union_of_isOpen h.right hs ht⟩

/-- If a function is continuous on open sets `s i`, it is continuous on their union -/
lemma ContinuousOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set α}
    (hf : ∀ i : ι, ContinuousOn f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).continuousAt ((hs i).mem_nhds hxsi) |>.continuousWithinAt

/-- A function is continuous on a union of open sets `s i` iff it is continuous on each `s i`. -/
lemma continuousOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set α}
    (hs : ∀ i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) ↔ ∀ i : ι, ContinuousOn f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContinuousOn.iUnion_of_isOpen h hs⟩

lemma continuous_of_continuousOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set α}
    (hf : ∀ i : ι, ContinuousOn f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Continuous f := by
  rw [← continuousOn_univ, ← hs']
  exact ContinuousOn.iUnion_of_isOpen hf hs

/-- If `f` is continuous on some neighbourhood `s'` of `s` and `f` maps `s` to `t`,
the preimage of a set neighbourhood of `t` is a set neighbourhood of `s`. -/
-- See `Continuous.tendsto_nhdsSet` for a special case.
theorem ContinuousOn.tendsto_nhdsSet {f : α → β} {s s' : Set α} {t : Set β}
    (hf : ContinuousOn f s') (hs' : s' ∈ 𝓝ˢ s) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) := by
  obtain ⟨V, hV, hsV, hVs'⟩ := mem_nhdsSet_iff_exists.mp hs'
  refine ((hasBasis_nhdsSet s).tendsto_iff (hasBasis_nhdsSet t)).mpr fun U hU ↦
    ⟨V ∩ f ⁻¹' U, ?_, fun _ ↦ ?_⟩
  · exact ⟨(hf.mono hVs').isOpen_inter_preimage hV hU.1,
      subset_inter hsV (hst.mono Subset.rfl hU.2)⟩
  · intro h
    rw [← mem_preimage]
    exact mem_of_mem_inter_right h

/-- Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighborhood of `s`
provided that `f` maps `s` to `t`. -/
theorem Continuous.tendsto_nhdsSet {f : α → β} {t : Set β} (hf : Continuous f)
    (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
  hf.continuousOn.tendsto_nhdsSet univ_mem hst

lemma Continuous.tendsto_nhdsSet_nhds
    {b : β} {f : α → β} (h : Continuous f) (h' : EqOn f (fun _ ↦ b) s) :
    Tendsto f (𝓝ˢ s) (𝓝 b) := by
  rw [← nhdsSet_singleton]
  exact h.tendsto_nhdsSet h'

lemma ContinuousOn.preimage_mem_nhdsSetWithin {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) {t u t' : Set β} (h : u ∈ 𝓝ˢ[t'] t) :
    f ⁻¹' u ∈ 𝓝ˢ[s ∩ f ⁻¹' t'] (s ∩ f ⁻¹' t) := by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
  · exact (inter_comm _ _).trans_subset <| (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc, ← hw.2, inter_comm _ s, inter_assoc, ← preimage_inter]
    exact inter_subset_right.trans <| preimage_mono hv.2.2

/-- If `f` is continuous on `s` and `u` is a neighbourhood of `t`, then `f ⁻¹' u` is a neighbourhood
of `s ∩ f ⁻¹' t` within `s`. -/
lemma ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) {t u : Set β} (h : u ∈ 𝓝ˢ t) : f ⁻¹' u ∈ 𝓝ˢ[s] (s ∩ f ⁻¹' t) := by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)

lemma Continuous.preimage_mem_nhdsSetWithin {f : α → β} (hf : Continuous f) {s u s' : Set β}
    (h : u ∈ 𝓝ˢ[s'] s) : f ⁻¹' u ∈ 𝓝ˢ[f ⁻¹' s'] (f ⁻¹' s) := by
  simpa using (hf.continuousOn (s := univ)).preimage_mem_nhdsSetWithin h

lemma Continuous.preimage_mem_nhdsSet {f : α → β} (hf : Continuous f) {s u : Set β}
    (h : u ∈ 𝓝ˢ s) : f ⁻¹' u ∈ 𝓝ˢ (f ⁻¹' s) := by
  simpa [h] using hf.preimage_mem_nhdsSetWithin (s := s) (u := u) (s' := univ)
