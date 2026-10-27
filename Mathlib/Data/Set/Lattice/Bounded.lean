/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Bounded and set-indexed unions and intersections

This file develops bounded indexed unions and intersections of sets, together with unions and
intersections indexed by sets of sets. It relates `biUnion` and `biInter` to subtype-indexed
families and relates `sUnion` and `sInter` to indexed families. It also contains results about
products of families of sets, directed unions, and reindexing along surjective functions.
-/

@[expose] public section

open Function

variable {α β γ : Type*} {ι ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

/-! ### Bounded unions and intersections -/

/-- A specialization of `mem_iUnion₂`. -/
theorem mem_biUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_iUnion₂_of_mem xs ytx

/-- A specialization of `mem_iInter₂`. -/
theorem mem_biInter {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
    y ∈ ⋂ x ∈ s, t x :=
  mem_iInter₂_of_mem h

/-- A specialization of `subset_iUnion₂`. -/
theorem subset_biUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
  subset_iUnion₂ (s := fun i _ => u i) x xs

/-- A specialization of `iInter₂_subset`. -/
theorem biInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    ⋂ x ∈ s, t x ⊆ t x :=
  iInter₂_subset x xs

lemma biInter_subset_biUnion {s : Set α} (hs : s.Nonempty) {t : α → Set β} :
    ⋂ x ∈ s, t x ⊆ ⋃ x ∈ s, t x := biInf_le_biSup hs

theorem biUnion_subset_biUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    ⋃ x ∈ s, t x ⊆ ⋃ x ∈ s', t x :=
  iUnion₂_subset fun _ hx => subset_biUnion_of_mem <| h hx

theorem biInter_subset_biInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    ⋂ x ∈ s, t x ⊆ ⋂ x ∈ s', t x :=
  subset_iInter₂ fun _ hx => biInter_subset_of_mem <| h hx

theorem biUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x :=
  (biUnion_subset_biUnion_left hs).trans <| iUnion₂_mono h

theorem biInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    ⋂ x ∈ s', t x ⊆ ⋂ x ∈ s, t' x :=
  (biInter_subset_biInter_left hs).trans <| iInter₂_mono h

theorem biUnion_eq_iUnion (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋃ x ∈ s, t x ‹_› = ⋃ x : s, t x x.2 :=
  iSup_subtype'

theorem biInter_eq_iInter (s : Set α) (t : ∀ x ∈ s, Set β) :
    ⋂ x ∈ s, t x ‹_› = ⋂ x : s, t x x.2 :=
  iInf_subtype'

@[simp] lemma biUnion_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋃ a ∈ s, t = t :=
  biSup_const hs

@[simp] lemma biInter_const {s : Set α} (hs : s.Nonempty) (t : Set β) : ⋂ a ∈ s, t = t :=
  biInf_const hs

theorem iUnion_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  iSup_subtype

theorem iInter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  iInf_subtype

theorem biInter_empty (u : α → Set β) : ⋂ x ∈ (∅ : Set α), u x = univ :=
  iInf_emptyset

theorem biInter_univ (u : α → Set β) : ⋂ x ∈ @univ α, u x = ⋂ x, u x :=
  iInf_univ

@[simp]
theorem biUnion_self (s : Set α) : ⋃ x ∈ s, s = s :=
  Subset.antisymm (iUnion₂_subset fun _ _ => Subset.refl s) fun _ hx => mem_biUnion hx hx

@[simp]
theorem iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Nonempty, s = s := by
  rw [iUnion_nonempty_index, biUnion_self]

@[simp] lemma iInter_ne_univ_self (s : Set α) : ⋂ _ : s ≠ univ, s = s :=
  compl_injective <| by simp [← nonempty_compl]

theorem biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Set α), s x = s a :=
  iInf_singleton

theorem biInter_union (s t : Set α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union

theorem biInter_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x := by simp

theorem biInter_pair (a b : α) (s : α → Set β) : ⋂ x ∈ ({a, b} : Set α), s x = s a ∩ s b := by
  rw [biInter_insert, biInter_singleton]

theorem biInter_inter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, f i ∩ t = (⋂ i ∈ s, f i) ∩ t := by
  have : Nonempty s := hs.to_subtype
  simp [biInter_eq_iInter, ← iInter_inter]

theorem inter_biInter {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋂ i ∈ s, t ∩ f i = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← biInter_inter hs]
  simp [inter_comm]

theorem biUnion_empty (s : α → Set β) : ⋃ x ∈ (∅ : Set α), s x = ∅ :=
  iSup_emptyset

theorem biUnion_univ (s : α → Set β) : ⋃ x ∈ @univ α, s x = ⋃ x, s x :=
  iSup_univ

theorem biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Set α), s x = s a :=
  iSup_singleton

@[simp]
theorem biUnion_of_singleton (s : Set α) : ⋃ x ∈ s, {x} = s :=
  ext <| by simp

theorem biUnion_union (s t : Set α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union

@[simp]
theorem iUnion_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋃ i, f i = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iUnion_subtype _ _

@[simp]
theorem iInter_coe_set {α β : Type*} (s : Set α) (f : s → Set β) :
    ⋂ i, f i = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  iInter_subtype _ _

theorem biUnion_insert (a : α) (s : Set α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x := by simp

theorem biUnion_pair (a b : α) (s : α → Set β) : ⋃ x ∈ ({a, b} : Set α), s x = s a ∪ s b := by
  simp

theorem inter_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_iUnion]

theorem iUnion₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [iUnion_inter]

theorem union_iInter₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_iInter]

theorem iInter₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [iInter_union]

theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀ S :=
  ⟨t, ht, hx⟩

-- is this theorem really necessary?
theorem notMem_of_notMem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩

theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  sInf_le tS

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
  le_sSup tS

theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀ S ⊆ t :=
  sSup_le h

@[simp]
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  sSup_le_iff

/-- `sUnion` is monotone under taking a subset of each set. -/
lemma sUnion_mono_subsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, t ⊆ f t) :
    ⋃₀ s ⊆ ⋃₀ (f '' s) :=
  fun _ ⟨t, htx, hxt⟩ ↦ ⟨f t, mem_image_of_mem f htx, hf t hxt⟩

/-- `sUnion` is monotone under taking a superset of each set. -/
lemma sUnion_mono_supsets {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, f t ⊆ t) :
    ⋃₀ (f '' s) ⊆ ⋃₀ s :=
  -- If t ∈ f '' s is arbitrary; t = f u for some u : Set α.
  fun _ ⟨_, ⟨u, hus, hut⟩, hxt⟩ ↦ ⟨u, hus, (hut ▸ hf u) hxt⟩

theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_sInf h

@[simp]
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  le_sInf_iff

@[gcongr]
theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
  sUnion_subset fun _ hs => subset_sUnion_of_mem (h hs)

@[gcongr]
theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun _ hs => sInter_subset_of_mem (h hs)

@[simp]
theorem sUnion_empty : ⋃₀ ∅ = (∅ : Set α) :=
  sSup_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  sInf_empty

@[simp]
theorem sUnion_singleton (s : Set α) : ⋃₀ {s} = s :=
  sSup_singleton

@[simp]
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  sInf_singleton

@[simp]
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  sSup_eq_bot

@[simp]
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  sInf_eq_top

theorem subset_powerset_iff {s : Set (Set α)} {t : Set α} : s ⊆ 𝒫 t ↔ ⋃₀ s ⊆ t :=
  sUnion_subset_iff.symm

/-- `⋃₀` and `𝒫` form a Galois connection. -/
theorem sUnion_powerset_gc :
    GaloisConnection (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  gc_sSup_Iic

/-- `⋃₀` and `𝒫` form a Galois insertion. -/
def sUnionPowersetGI :
    GaloisInsertion (⋃₀ · : Set (Set α) → Set α) (𝒫 · : Set α → Set (Set α)) :=
  giSSupIic

/-- If all sets in a collection are either `∅` or `Set.univ`, then so is their union. -/
theorem sUnion_mem_empty_univ {S : Set (Set α)} (h : S ⊆ {∅, univ}) :
    ⋃₀ S ∈ ({∅, univ} : Set (Set α)) := by
  grind

@[simp]
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]

theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀ s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩

theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ) : s.Nonempty :=
  Nonempty.of_sUnion <| h.symm ▸ univ_nonempty

theorem sUnion_union (S T : Set (Set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
  sSup_union

theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  sInf_union

@[simp]
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s ∪ ⋃₀ T :=
  sSup_insert

@[simp]
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  sInf_insert

@[simp]
theorem sUnion_sdiff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
  sSup_sdiff_singleton_bot s

@[deprecated (since := "2026-06-03")]
alias sUnion_diff_singleton_empty := sUnion_sdiff_singleton_empty

@[simp]
theorem sInter_sdiff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  sInf_sdiff_singleton_top s

@[deprecated (since := "2026-06-03")]
alias sInter_diff_singleton_univ := sInter_sdiff_singleton_univ

theorem sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s ∪ t :=
  sSup_pair

theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  sInf_pair

@[simp]
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ a ∈ s, f a :=
  sSup_image

@[simp]
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ a ∈ s, f a :=
  sInf_image

@[simp]
lemma sUnion_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋃₀ (image2 f s t) = ⋃ (a ∈ s) (b ∈ t), f a b := sSup_image2

@[simp]
lemma sInter_image2 (f : α → β → Set γ) (s : Set α) (t : Set β) :
    ⋂₀ (image2 f s t) = ⋂ (a ∈ s) (b ∈ t), f a b := sInf_image2

@[simp]
theorem sUnion_range (f : ι → Set β) : ⋃₀ range f = ⋃ x, f x :=
  rfl

@[simp]
theorem sInter_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl

theorem iUnion_eq_univ_iff {f : ι → Set α} : ⋃ i, f i = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_iUnion]

theorem iUnion₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    ⋃ (i) (j), s i j = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by
  simp only [iUnion_eq_univ_iff, mem_iUnion]

theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]

theorem iInter_eq_empty_of_eq_empty {i : ι} {f : ι → Set α} (h : f i = ∅) :
    ⋂ j, f j = ∅ :=
  subset_eq_empty (iInter_subset _ i) h

-- classical
theorem iInter_eq_empty_iff {f : ι → Set α} : ⋂ i, f i = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
theorem iInter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    ⋂ (i) (j), s i j = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_notMem, mem_iInter, not_forall]

-- classical
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_notMem]

-- classical
@[simp]
theorem nonempty_iInter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, iInter_eq_empty_iff]

-- classical
theorem nonempty_iInter₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp

-- classical
@[simp]
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]

-- classical
theorem compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp

-- classical
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h]; exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)

theorem range_sigma_eq_iUnion_range {γ : α → Type*} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp

theorem iUnion_eq_range_sigma (s : α → Set β) : ⋃ i, s i = range fun a : Σ i, s i => a.2 := by
  simp [Set.ext_iff]

theorem iUnion_eq_range_psigma (s : ι → Set β) : ⋃ i, s i = range fun a : Σ' i, s i => a.2 := by
  simp [Set.ext_iff]

theorem iUnion_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : Set (Sigma σ)) :
    ⋃ i, Sigma.mk i '' Sigma.mk i ⁻¹' s = s := by
  ext x
  simp only [mem_iUnion, mem_image, mem_preimage]
  grind

theorem Sigma.univ (X : α → Type*) : (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩

alias sUnion_mono := sUnion_subset_sUnion

alias sInter_mono := sInter_subset_sInter

theorem iUnion_subset_iUnion_const {s : Set α} (h : ι → ι₂) : ⋃ _ : ι, s ⊆ ⋃ _ : ι₂, s :=
  iSup_const_mono (α := Set α) h

@[simp]
theorem iUnion_singleton_eq_range (f : α → β) : ⋃ x : α, {f x} = range f := by
  ext x
  simp [@eq_comm _ x]

theorem iUnion_insert_eq_range_union_iUnion {ι : Type*} (x : ι → β) (t : ι → Set β) :
    ⋃ i, insert (x i) (t i) = range x ∪ ⋃ i, t i := by
  simp_rw [← union_singleton, iUnion_union_distrib, union_comm, iUnion_singleton_eq_range]

theorem iUnion_of_singleton (α : Type*) : (⋃ x, {x} : Set α) = univ := by simp [Set.ext_iff]

theorem iUnion_of_singleton_coe (s : Set α) : ⋃ i : s, ({(i : α)} : Set α) = s := by simp

theorem sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (_ : i ∈ s), i := by
  rw [← sUnion_image, image_id']

theorem sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (_ : i ∈ s), i := by
  rw [← sInter_image, image_id']

theorem sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]

theorem sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]

@[simp]
theorem iUnion_of_empty [IsEmpty ι] (s : ι → Set α) : ⋃ i, s i = ∅ :=
  iSup_of_empty _

@[simp]
theorem iInter_of_empty [IsEmpty ι] (s : ι → Set α) : ⋂ i, s i = univ :=
  iInf_of_empty _

theorem union_eq_iUnion {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_iSup s₁ s₂

theorem inter_eq_iInter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_iInf s₁ s₂

theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  sInf_sup_sInf

theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀ s ∩ ⋃₀ t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  sSup_inf_sSup

theorem biUnion_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by simp [@iUnion_comm _ ι]

theorem biInter_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋂ x ∈ ⋃ i, s i, t x = ⋂ (i) (x ∈ s i), t x := by simp [@iInter_comm _ ι]

theorem sUnion_iUnion (s : ι → Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i := by
  simp only [sUnion_eq_biUnion, biUnion_iUnion]

theorem sInter_iUnion (s : ι → Set (Set α)) : ⋂₀ ⋃ i, s i = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_biInter, biInter_iUnion]

theorem iUnion_range_eq_sUnion {α β : Type*} (C : Set (Set α)) {f : ∀ s : C, β → (s : Type _)}
    (hf : ∀ s : C, Surjective (f s)) : ⋃ y : β, range (fun s : C => (f s y).val) = ⋃₀ C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine ⟨_, hs, ?_⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := hf ⟨s, hs⟩ ⟨x, hx⟩
    refine ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, ?_⟩
    exact congr_arg Subtype.val hy

theorem iUnion_range_eq_iUnion (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : ⋃ y : β, range (fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_iUnion, mem_iUnion]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    obtain ⟨y, hy⟩ := hf i ⟨x, hx⟩
    exact ⟨y, i, congr_arg Subtype.val hy⟩

lemma iUnion_sumElim {ι σ : Type*} (s : ι → Set α) (t : σ → Set α) :
    ⋃ x, Sum.elim s t x = (⋃ x, s x) ∪ ⋃ x, t x := by
  ext
  simp

theorem union_distrib_iInter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_iInf_eq _ _

theorem union_distrib_iInter₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_iInter_left]

theorem union_distrib_iInter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  iInf_sup_eq _ _

theorem union_distrib_iInter₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_iInter_right]

lemma biUnion_lt_eq_iUnion [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋃ (n) (m < n), s m = ⋃ n, s n := biSup_lt_eq_iSup

lemma biUnion_le_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≤ n), s m = ⋃ n, s n := biSup_le_eq_iSup

lemma biInter_lt_eq_iInter [LT α] [NoMaxOrder α] {s : α → Set β} :
    ⋂ (n) (m < n), s m = ⋂ (n), s n := biInf_lt_eq_iInf

lemma biInter_le_eq_iInter [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≤ n), s m = ⋂ (n), s n := biInf_le_eq_iInf

lemma biUnion_gt_eq_iUnion [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋃ (n) (m > n), s m = ⋃ n, s n := biSup_gt_eq_iSup

lemma biUnion_ge_eq_iUnion [Preorder α] {s : α → Set β} :
    ⋃ (n) (m ≥ n), s m = ⋃ n, s n := biSup_ge_eq_iSup

lemma biInter_gt_eq_iInf [LT α] [NoMinOrder α] {s : α → Set β} :
    ⋂ (n) (m > n), s m = ⋂ n, s n := biInf_gt_eq_iInf

lemma biInter_ge_eq_iInf [Preorder α] {s : α → Set β} :
    ⋂ (n) (m ≥ n), s m = ⋂ n, s n := biInf_ge_eq_iInf

section le

variable {ι : Type*} [PartialOrder ι] (s : ι → Set α) (i : ι)

theorem biUnion_le : (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
  biSup_le_eq_sup s i

theorem biInter_le : (⋂ j ≤ i, s j) = (⋂ j < i, s j) ∩ s i :=
  biInf_le_eq_inf s i

theorem biUnion_ge : (⋃ j ≥ i, s j) = s i ∪ ⋃ j > i, s j :=
  biSup_ge_eq_sup s i

theorem biInter_ge : (⋂ j ≥ i, s j) = s i ∩ ⋂ j > i, s j :=
  biInf_ge_eq_inf s i

end le

section Pi

variable {π : α → Type*}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp

theorem univ_pi_eq_iInter (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, iInter_true, mem_univ]

theorem pi_sdiff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine sdiff_subset_comm.2 fun x hx a ha => ?_
  simp only [mem_sdiff, mem_pi, mem_iUnion, not_exists, mem_preimage, not_and, not_not] at hx
  exact hx.2 _ ha (hx.1 _ ha)

@[deprecated (since := "2026-06-03")] alias pi_diff_pi_subset := pi_sdiff_pi_subset

theorem iUnion_univ_pi {ι : α → Type*} (t : (a : α) → ι a → Set (π a)) :
    ⋃ x : (a : α) → ι a, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j : ι a, t a j := by
  ext
  simp [Classical.skolem]

theorem biUnion_univ_pi {ι : α → Type*} (s : (a : α) → Set (ι a)) (t : (a : α) → ι a → Set (π a)) :
    ⋃ x ∈ univ.pi s, pi univ (fun a => t a (x a)) = pi univ fun a => ⋃ j ∈ s a, t a j := by
  ext
  simp [Classical.skolem, forall_and]

theorem pi_iUnion_eq_iInter_pi {α' : Type*} (s : α' → Set α) (t : (a : α) → Set (π a)) :
    (⋃ i, s i).pi t = ⋂ i, (s i).pi t := by
  ext f
  simp
  grind

end Pi

section Directed

theorem directedOn_iUnion {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, mem_iUnion, exists_imp]
  exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
    let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
    let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
    ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

theorem directedOn_sUnion {r} {S : Set (Set α)} (hd : DirectedOn (· ⊆ ·) S)
    (h : ∀ x ∈ S, DirectedOn r x) : DirectedOn r (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact directedOn_iUnion (directedOn_iff_directed.mp hd) (fun i ↦ h i.1 i.2)
end Directed

end Set

namespace Function

namespace Surjective

theorem iUnion_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋃ x, g (f x) = ⋃ y, g y :=
  hf.iSup_comp g

theorem iInter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : ⋂ x, g (f x) = ⋂ y, g y :=
  hf.iInf_comp g

end Surjective

end Function

namespace Set

variable (t : α → Set β)

theorem biUnion_sdiff_biUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [sdiff_subset_iff, ← biUnion_union]
  apply biUnion_subset_biUnion_left
  rw [union_sdiff_self]
  apply subset_union_right

@[deprecated (since := "2026-06-03")]
alias biUnion_diff_biUnion_subset := biUnion_sdiff_biUnion_subset

end Set
