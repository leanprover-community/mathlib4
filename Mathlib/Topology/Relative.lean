/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Constructions

/-!
# Relative open/closed sets

We define open and closed sets relative to another set. Specifically, `t` is open/closed in `s`
whenever the intersection `s ∩ t` is open/closed in the subtype topology of `s`.

## Main definitions

- `IsOpenIn s t`: `t` is open in `s`
- `IsClosedIn s t`: `t` is closed in `s`
-/

open Set.Notation Set

variable {X α : Type*} {ι : Sort*} {s t u : Set X} [TopologicalSpace X]

/-- A set `t` is open in `s` when the intersection `s ∩ t` is open in the subtype topology of
`s`. -/
def IsOpenIn (s : Set X) (t : Set X) : Prop :=
  IsOpen (s ↓∩ t)

theorem IsOpen.isOpenIn (s : Set X) (ht : IsOpen t) : IsOpenIn s t :=
  ⟨t, ht, rfl⟩

theorem isOpenIn_empty_left (s : Set X) : IsOpenIn ∅ s :=
  isOpen_discrete _

theorem isOpenIn_empty_right (s : Set X) : IsOpenIn s ∅ :=
  isOpen_empty

theorem isOpenIn_univ (s : Set X) : IsOpenIn s univ :=
  isOpen_univ

@[simp]
theorem isOpenIn_univ_iff : IsOpenIn univ s ↔ IsOpen s := by
  refine ⟨fun ⟨a, ha, ha'⟩ ↦ ?_, IsOpen.isOpenIn _⟩
  apply_fun (Subtype.val '' ·) at ha'
  convert ← ha
  simpa using ha'

theorem IsOpenIn.union (hs : IsOpenIn s t) (ht : IsOpenIn s u) : IsOpenIn s (t ∪ u) :=
  IsOpen.union hs ht

theorem IsOpenIn.inter (hs : IsOpenIn s t) (ht : IsOpenIn s u) : IsOpenIn s (t ∩ u) :=
  IsOpen.inter hs ht

theorem isOpenIn_sUnion {t : Set (Set X)} (h : ∀ u, u ∈ t → IsOpenIn s u) :
    IsOpenIn s (⋃₀ t) := by
  rw [IsOpenIn, preimage_val_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

theorem isOpenIn_iUnion {f : ι → Set X} (h : ∀ i : ι, IsOpenIn s (f i)) :
    IsOpenIn s (⋃ i, f i) :=
  isOpenIn_sUnion (forall_mem_range.2 h)

theorem isOpenIn_biUnion {t : Set α} {f : α → Set X} (h : ∀ i ∈ t, IsOpenIn s (f i)) :
    IsOpenIn s (⋃ i ∈ t, f i) :=
  isOpenIn_iUnion fun i => isOpenIn_iUnion fun hi => h i hi

/-- A set `t` is closed in `s` when the intersection `s ∩ t` is closed in the subtype topology of
`s`. -/
def IsClosedIn (s : Set X) (t : Set X) : Prop :=
  IsClosed (s ↓∩ t)

@[simp]
theorem isOpenIn_compl_iff : IsOpenIn s tᶜ ↔ IsClosedIn s t :=
  isOpen_compl_iff

@[simp]
theorem isClosedIn_compl_iff : IsClosedIn s tᶜ ↔ IsOpenIn s t :=
  isClosed_compl_iff

theorem IsClosed.IsClosedIn (s : Set X) (ht : IsClosed t) : IsClosedIn s t := by
  rw [← isOpen_compl_iff] at ht
  rw [← isOpenIn_compl_iff]
  exact ht.isOpenIn _

theorem isClosedIn_empty_left (s : Set X) : IsClosedIn ∅ s :=
  isClosed_discrete _

theorem isClosedIn_empty_right (s : Set X) : IsClosedIn s ∅ :=
  isClosed_empty

theorem isClosedIn_univ (s : Set X) : IsClosedIn s univ :=
  isClosed_univ

@[simp]
theorem isClosedIn_univ_iff : IsClosedIn univ s ↔ IsClosed s := by
  rw [← isOpenIn_compl_iff, isOpenIn_univ_iff, isOpen_compl_iff]

theorem IsClosedIn.union (hs : IsClosedIn s t) (ht : IsClosedIn s u) : IsClosedIn s (t ∪ u) :=
  IsClosed.union hs ht

theorem IsClosedIn.inter (hs : IsClosedIn s t) (ht : IsClosedIn s u) : IsClosedIn s (t ∩ u) :=
  IsClosed.inter hs ht

theorem isClosedIn_sInter {t : Set (Set X)} (h : ∀ u, u ∈ t → IsClosedIn s u) :
    IsClosedIn s (⋂₀ t) := by
  rw [IsClosedIn, preimage_sInter]
  exact isClosed_biInter h

theorem isClosedIn_iInter {f : ι → Set X} (h : ∀ i : ι, IsClosedIn s (f i)) :
    IsClosedIn s (⋂ i, f i) :=
  isClosedIn_sInter (forall_mem_range.2 h)

theorem isClosedIn_biInter {t : Set α} {f : α → Set X} (h : ∀ i ∈ t, IsClosedIn s (f i)) :
    IsClosedIn s (⋂ i ∈ t, f i) :=
  isClosedIn_iInter fun i => isClosedIn_iInter fun hi => h i hi
