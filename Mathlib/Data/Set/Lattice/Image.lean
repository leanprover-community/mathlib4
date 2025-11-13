/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Monotonicity.Attr

/-!
# The set lattice and (pre)images of functions

This file contains lemmas on the interaction between the indexed union/intersection of sets
and the image and preimage operations: `Set.image`, `Set.preimage`, `Set.image2`, `Set.kernImage`.
It also covers `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`.

In order to accommodate `Set.image2`, the file includes results on union/intersection in products.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff

protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun _ _ =>
  subset_kernImage_iff.symm

end GaloisConnection

section kernImage

variable {f : α → β}

lemma kernImage_mono : Monotone (kernImage f) :=
  Set.preimage_kernImage.monotone_u

lemma kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ :=
  Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t ↦ compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

lemma kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ := by
  rw [kernImage_eq_compl, compl_compl]

lemma kernImage_empty : kernImage f ∅ = (range f)ᶜ := by
  rw [kernImage_eq_compl, compl_empty, image_univ]

lemma kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ ⊆ s := by
  rw [kernImage_eq_compl, ← preimage_compl, compl_eq_comm, eq_comm, image_preimage_eq_iff,
      compl_subset_comm]

lemma compl_range_subset_kernImage {s : Set α} : (range f)ᶜ ⊆ kernImage f s := by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

lemma kernImage_union_preimage {s : Set α} {t : Set β} :
    kernImage f (s ∪ f ⁻¹' t) = kernImage f s ∪ t := by
  rw [kernImage_eq_compl, kernImage_eq_compl, compl_union, ← preimage_compl, image_inter_preimage,
      compl_inter, compl_compl]

lemma kernImage_preimage_union {s : Set α} {t : Set β} :
    kernImage f (f ⁻¹' t ∪ s) = t ∪ kernImage f s := by
  rw [union_comm, kernImage_union_preimage, union_comm]

end kernImage

theorem image_projection_prod {ι : Type*} {α : ι → Type*} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

/-! ### Bounded unions and intersections -/

section Function

/-! ### Lemmas about `Set.MapsTo` -/

@[simp]
theorem mapsTo_sUnion {S : Set (Set α)} {t : Set β} {f : α → β} :
    MapsTo f (⋃₀ S) t ↔ ∀ s ∈ S, MapsTo f s t :=
  sUnion_subset_iff

@[simp]
theorem mapsTo_iUnion {s : ι → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ i, s i) t ↔ ∀ i, MapsTo f (s i) t :=
  iUnion_subset_iff

theorem mapsTo_iUnion₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ (i) (j), s i j) t ↔ ∀ i j, MapsTo f (s i j) t :=
  iUnion₂_subset_iff

theorem mapsTo_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  mapsTo_iUnion.2 fun i ↦ (H i).mono_right (subset_iUnion t i)

theorem mapsTo_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)

@[simp]
theorem mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α → β} :
    MapsTo f s (⋂₀ T) ↔ ∀ t ∈ T, MapsTo f s t :=
  forall₂_swap

@[simp]
theorem mapsTo_iInter {s : Set α} {t : ι → Set β} {f : α → β} :
    MapsTo f s (⋂ i, t i) ↔ ∀ i, MapsTo f s (t i) :=
  mapsTo_sInter.trans forall_mem_range

theorem mapsTo_iInter₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β} :
    MapsTo f s (⋂ (i) (j), t i j) ↔ ∀ i j, MapsTo f s (t i j) := by
  simp only [mapsTo_iInter]

theorem mapsTo_iInter_iInter {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)

theorem mapsTo_iInter₂_iInter₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)

theorem image_iInter_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset

theorem image_iInter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset

theorem image_sInter_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset

theorem image2_sInter_right_subset (t : Set α) (S : Set (Set β)) (f : α → β → γ) :
    image2 f t (⋂₀ S) ⊆ ⋂ s ∈ S, image2 f t s := by
  aesop

theorem image2_sInter_left_subset (S : Set (Set α)) (t : Set β) (f : α → β → γ) :
    image2 f (⋂₀ S) t ⊆ ⋂ s ∈ S, image2 f s t := by
  aesop

/-! ### `restrictPreimage` -/


section

open Function

variable {f : α → β} {U : ι → Set β} (hU : iUnion U = univ)
include hU

theorem injective_iff_injective_of_iUnion_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x ∈ Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)

theorem surjective_iff_surjective_of_iUnion_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x ∈ Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩

theorem bijective_iff_bijective_of_iUnion_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  rw [Bijective, injective_iff_injective_of_iUnion_eq_univ hU,
    surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]

end

/-! ### `InjOn` -/


theorem InjOn.image_iInter_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]

theorem InjOn.image_biInter_eq {p : ι → Prop} {s : ∀ i, p i → Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [iInter, iInf_subtype']
  haveI : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h

theorem image_iInter {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq

theorem image_iInter₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_iInter hf]

theorem inj_on_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy

/-! ### `SurjOn` -/


theorem surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀ T) := fun _ ⟨t, ht, hx⟩ => H t ht hx

theorem surjOn_iUnion {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surjOn_sUnion <| forall_mem_range.2 H

theorem surjOn_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)

theorem surjOn_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surjOn_iUnion fun i => surjOn_iUnion (H i)

theorem surjOn_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)

theorem surjOn_iInter [Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_iInter_eq, mem_iInter]
  exact fun i => H i hy

theorem surjOn_iInter_iInter [Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj

/-! ### `BijOn` -/


theorem bijOn_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩

theorem bijOn_iInter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩

theorem bijOn_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bijOn_iUnion H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn

theorem bijOn_iInter_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bijOn_iInter H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn

end Function

/-! ### `image`, `preimage` -/


section Image

theorem image_iUnion {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, exists_swap (α := α)]

theorem image_iUnion₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_iUnion]

theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]

theorem range_eq_iUnion {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]

theorem image_eq_iUnion (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]

theorem biUnion_range {f : ι → α} {g : α → Set β} : ⋃ x ∈ range f, g x = ⋃ y, g (f y) :=
  iSup_range

@[simp]
theorem iUnion_iUnion_eq' {f : ι → α} {g : α → Set β} :
    ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y) := by simpa using biUnion_range

theorem biInter_range {f : ι → α} {g : α → Set β} : ⋂ x ∈ range f, g x = ⋂ y, g (f y) :=
  iInf_range

@[simp]
theorem iInter_iInter_eq' {f : ι → α} {g : α → Set β} :
    ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y) := by simpa using biInter_range

variable {s : Set γ} {f : γ → α} {g : α → Set β}

theorem biUnion_image : ⋃ x ∈ f '' s, g x = ⋃ y ∈ s, g (f y) :=
  iSup_image

theorem biInter_image : ⋂ x ∈ f '' s, g x = ⋂ y ∈ s, g (f y) :=
  iInf_image

lemma biUnion_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋃ c ∈ image2 f s t, g c = ⋃ a ∈ s, ⋃ b ∈ t, g (f a b) := iSup_image2 ..

lemma biInter_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋂ c ∈ image2 f s t, g c = ⋂ a ∈ s, ⋂ b ∈ t, g (f a b) := iInf_image2 ..

lemma iUnion_inter_iUnion {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋃ i, f i) ∩ ⋃ j, g j = ⋃ i, ⋃ j, f i ∩ g j := by simp_rw [iUnion_inter, inter_iUnion]

lemma iInter_union_iInter {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋂ i, f i) ∪ ⋂ j, g j = ⋂ i, ⋂ j, f i ∪ g j := by simp_rw [iInter_union, union_iInter]

lemma iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋃ i₁, ⋃ i₂, f i₁ i₂) ∩ ⋃ j₁, ⋃ j₂, g j₁ j₂ = ⋃ i₁, ⋃ i₂, ⋃ j₁, ⋃ j₂, f i₁ i₂ ∩ g j₁ j₂ := by
  simp_rw [iUnion_inter, inter_iUnion]

lemma iInter₂_union_iInter₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋂ i₁, ⋂ i₂, f i₁ i₂) ∪ ⋂ j₁, ⋂ j₂, g j₁ j₂ = ⋂ i₁, ⋂ i₂, ⋂ j₁, ⋂ j₂, f i₁ i₂ ∪ g j₁ j₂ := by
  simp_rw [iInter_union, union_iInter]

theorem biUnion_inter_of_pairwise_disjoint {ι : Type*} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⋃ i ∈ (s ∩ t), f i) = (⋃ i ∈ s, f i) ∩ (⋃ i ∈ t, f i) :=
  biSup_inter_of_pairwise_disjoint h s t

theorem biUnion_iInter_of_pairwise_disjoint {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι → Set α} (h : Pairwise (Disjoint on f)) (s : κ → Set ι) :
    (⋃ i ∈ (⋂ j, s j), f i) = ⋂ j, (⋃ i ∈ s j, f i) :=
  biSup_iInter_of_pairwise_disjoint h s

end Image

section Preimage

theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun _ _ h => preimage_mono h

@[simp]
theorem preimage_iUnion {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]

theorem preimage_iUnion₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iUnion]

theorem image_sUnion {f : α → β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by
  ext b
  simp only [mem_image, mem_sUnion, exists_prop, sUnion_image, mem_iUnion]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩

@[simp]
theorem preimage_sUnion {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀ s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_biUnion, preimage_iUnion₂]

theorem preimage_iInter {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext; simp

theorem preimage_iInter₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iInter]

@[simp]
theorem preimage_sInter {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_biInter, preimage_iInter₂]

@[simp]
theorem biUnion_preimage_singleton (f : α → β) (s : Set β) : ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s := by
  rw [← preimage_iUnion₂, biUnion_of_singleton]

theorem biUnion_range_preimage_singleton (f : α → β) : ⋃ y ∈ range f, f ⁻¹' {y} = univ := by
  rw [biUnion_preimage_singleton, preimage_range]

end Preimage

section Prod

theorem prod_iUnion {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp

theorem prod_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_iUnion]

theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]

theorem iUnion_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp

theorem iUnion₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [iUnion_prod_const]

theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀ C ×ˢ t = ⋃₀ ((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]

theorem iUnion_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    ⋃ x : ι × ι', s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp

/-- Analogue of `iSup_prod` for sets. -/
lemma iUnion_prod' (f : β × γ → Set α) : ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j) :=
  iSup_prod

theorem iUnion_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : ⋃ x, s x ×ˢ t x = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩

lemma biUnion_prod {α β γ} (s : Set α) (t : Set β) (f : α → Set γ) (g : β → Set δ) :
    ⋃ x ∈ s ×ˢ t, f x.1 ×ˢ g x.2 = (⋃ x ∈ s, f x) ×ˢ (⋃ x ∈ t, g x) := by
  ext ⟨_, _⟩
  simp only [mem_iUnion, mem_prod, exists_prop, Prod.exists]; tauto

/-- Analogue of `biSup_prod` for sets. -/
lemma biUnion_prod' (s : Set β) (t : Set γ) (f : β × γ → Set α) :
    ⋃ x ∈ s ×ˢ t, f x = ⋃ (i ∈ s) (j ∈ t), f (i, j) :=
  biSup_prod

theorem sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩

theorem sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩

theorem sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) :
    ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t := by
  rw [← sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

theorem prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) :
    s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t := by
  rw [← sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]

theorem prod_iInter {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i := by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

/-- The `Set.image2` version of `Set.image_eq_iUnion` -/
theorem image2_eq_iUnion (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  ext; simp [eq_comm]

theorem iUnion_image_left : ⋃ a ∈ s, f a '' t = image2 f s t := by
  simp only [image2_eq_iUnion, image_eq_iUnion]

theorem iUnion_image_right : ⋃ b ∈ t, (f · b) '' s = image2 f s t := by
  rw [image2_swap, iUnion_image_left]

theorem image2_iUnion_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]

theorem image2_iUnion_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_iUnion, image_iUnion]

theorem image2_sUnion_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋃₀ S) t = ⋃ s ∈ S, image2 f s t := by
  aesop

theorem image2_sUnion_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋃₀ T) = ⋃ t ∈ T, image2 f s t := by
  aesop

theorem image2_iUnion₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_iUnion_left]

theorem image2_iUnion₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_iUnion_right]

theorem image2_iInter_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy

theorem image2_iInter_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)

theorem image2_iInter₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy

theorem image2_iInter₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)

theorem image2_sInter_subset_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋂₀ S) t ⊆ ⋂ s ∈ S, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_left ..

theorem image2_sInter_subset_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋂₀ T) ⊆ ⋂ t ∈ T, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_right ..

theorem prod_eq_biUnion_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [iUnion_image_left, image2_mk_eq_prod]

theorem prod_eq_biUnion_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [iUnion_image_right, image2_mk_eq_prod]

end Image2

section Seq

theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t := by
  rw [seq_eq_image2, iUnion_image_left]

theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  image2_subset_iff

@[gcongr, mono]
theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := image2_subset hs ht

theorem singleton_seq {f : α → β} {t : Set α} : Set.seq ({f} : Set (α → β)) t = f '' t :=
  image2_singleton_left

theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  image2_singleton_right

theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  simp only [seq_eq_image2, image2_image_left]
  exact .symm <| image2_assoc fun _ _ _ ↦ rfl

theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((f ∘ ·) '' s) t := by
  simp only [seq, image_image2, image2_image_left, comp_apply]

theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  rw [seq_eq_image2, image2_image_left, image2_mk_eq_prod]

theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp]; rfl

theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  rw [seq_eq_image2, image2_image_left]

end Seq

end Set
