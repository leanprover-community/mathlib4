/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Topology.GDelta

/-!
## Nowhere dense and meagre sets
Define nowhere dense and meagre sets (`IsNowhereDense` and `IsMeagre`, respectively)
and prove their basic properties.

Main properties:
- `closure_nowhere_dense`: the closure of a nowhere dense set is nowhere dense
- `closed_nowhere_dense_iff_complement`: a closed set is nowhere dense iff
its complement is open and dense
- `meagre_iff_complement_comeagre`: a set is nowhere dense iff its complement is `residual`.
- `empty_mono`: subsets of meagre sets are meagre
- `meagre_iUnion`: countable unions of meagre sets are meagre
-/

open Function TopologicalSpace Set
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α]

/-- A set is nowhere dense iff its closure has empty interior. -/
def IsNowhereDense (s : Set α) := IsEmpty (interior (closure s))

/-- A closed set is nowhere dense iff its interior is empty. -/
lemma closed_nowhere_dense_iff {s : Set α} (hs : IsClosed s) : IsNowhereDense s ↔ IsEmpty (interior s) := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]

/-- If a set `s` is nowhere dense, so is its closure.-/
lemma closure_nowhere_dense {s : Set α} (hs : IsNowhereDense s) : IsNowhereDense (closure s) := by
  rw [IsNowhereDense, closure_closure]
  exact hs

/-- A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its closure). -/
lemma nowhere_dense_contained_in_closed_nowhere_dense {s : Set α} (hs : IsNowhereDense s) :
    ∃ t : Set α, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t := by
  use closure s
  exact ⟨subset_closure, ⟨closure_nowhere_dense hs, isClosed_closure⟩⟩

/-- A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense. -/
lemma closed_nowhere_dense_iff_complement {s : Set α} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  constructor
  · rintro ⟨hclosed, hNowhereDense⟩
    constructor
    · exact Iff.mpr isOpen_compl_iff hclosed
    · rw [← interior_eq_empty_iff_dense_compl]
      rw [closed_nowhere_dense_iff hclosed] at hNowhereDense
      exact Iff.mp isEmpty_coe_sort hNowhereDense
  · rintro ⟨hopen, hdense⟩
    constructor
    · exact { isOpen_compl := hopen }
    · have : IsClosed s := by exact { isOpen_compl := hopen }
      rw [closed_nowhere_dense_iff this, isEmpty_coe_sort, interior_eq_empty_iff_dense_compl]
      exact hdense

/-- A set is **meagre** iff it is contained in the countable union of nowhere dense sets. -/
def IsMeagre (s : Set α) := ∃ S : Set (Set α), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S

-- TODO: move to the right place!
lemma sUnion_subset_mono1 {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, t ⊆ f t) :
    ⋃₀ s ⊆ ⋃₀ (f '' s) := by
  rintro x ⟨t, htx, hxt⟩
  use f t
  exact ⟨mem_image_of_mem f htx, hf t hxt⟩

lemma sUnion_subset_mono2 {s : Set (Set α)} {f : Set α → Set α} (hf : ∀ t : Set α, t ⊇ f t) :
    ⋃₀ s ⊇ ⋃₀ (f '' s) := by
  -- let t ∈ f '' s be arbitrary; then t = f u for some u : Set α
  rintro x ⟨t, ⟨u, hus, hut⟩, hxt⟩
  have : u ⊇ t := by rw [← hut]; exact hf u
  rw [mem_sUnion]
  use u
  exact ⟨hus, this hxt⟩

lemma sUnion_subset_closure {s : Set (Set α)} : ⋃₀ s ⊆ ⋃₀ (closure '' s) :=
  sUnion_subset_mono1 (by apply subset_closure)

lemma sUnion_supset_interior {s : Set (Set α)} : ⋃₀ (interior '' s) ⊆ ⋃₀ s:=
  sUnion_subset_mono2 (by apply interior_subset)

/-- A set is meagre iff its complement is residual (or comeagre). -/
lemma meagre_iff_complement_comeagre {s : Set α} : IsMeagre s ↔ sᶜ ∈ residual α := by
  constructor
  · rintro ⟨s', ⟨hnowhereDense, hcountable, hss'⟩⟩
    -- Passing to the closure, assume all U_i are closed nowhere dense.
    let s'' := closure '' s'
    have hnowhereDense' : ∀ (t : Set α), t ∈ s'' → IsClosed t ∧ IsNowhereDense t := by
      rintro t ⟨x, hx, hclosed⟩
      rw [← hclosed]
      exact ⟨isClosed_closure, closure_nowhere_dense (hnowhereDense x hx)⟩
    have hcountable' : Set.Countable s'' := Countable.image hcountable _
    have hss'' : s ⊆ ⋃₀ s'' := calc
      s ⊆ ⋃₀ s' := hss'
      _ ⊆ ⋃₀ s'' := sUnion_subset_closure
    -- Then each U_i^c is open and dense.
    have h : ∀ (t : Set α), t ∈ s'' → IsOpen tᶜ ∧ Dense tᶜ  :=
      fun t ht ↦ Iff.mp closed_nowhere_dense_iff_complement (hnowhereDense' t ht)
    let complement := compl '' s''
    have h' : ∀ (t : Set α), t ∈ complement → IsOpen t ∧ Dense t := by
      rintro t ⟨x, hx, hcompl⟩
      rw [← hcompl]
      exact h x hx
    -- and we compute ⋂ U_iᶜ ⊆ sᶜ, completing the proof.
    have h2: ⋂₀ complement ⊆ sᶜ := calc ⋂₀ complement
        _ = (⋃₀ s'')ᶜ := by rw [←compl_sUnion]
        _ ⊆ sᶜ := Iff.mpr compl_subset_compl hss''
    rw [mem_residual_iff]
    use complement
    constructor
    · intro t ht
      exact (h' t ht).1
    · constructor
      · intro t ht
        exact (h' t ht).2
      · exact ⟨Countable.image hcountable' compl, h2⟩
  · intro hs -- suppose sᶜ is comeagre, then sᶜ ⊇ ⋂ U i for open dense sets U_i
    rw [mem_residual_iff] at hs
    rcases hs with ⟨s', ⟨hopen, hdense, hcountable, hss'⟩⟩
    have h : s ⊆ ⋃₀ (compl '' s') := calc
      s = sᶜᶜ := by rw [compl_compl s]
      _ ⊆ (⋂₀ s')ᶜ := Iff.mpr compl_subset_compl hss'
      _ = ⋃₀ (compl '' s') := by rw [compl_sInter]
    -- Each u_iᶜ is closed and nowhere dense, hence nowhere dense.
    have : ∀ t : Set α, t ∈ s' → IsClosed tᶜ ∧ IsNowhereDense tᶜ := by
      intro t ht
      have : IsOpen tᶜᶜ ∧ Dense tᶜᶜ := by
        rw [compl_compl]
        exact ⟨hopen t ht, hdense t ht⟩
      exact Iff.mpr closed_nowhere_dense_iff_complement this
    have : ∀ t : Set α, t ∈ s' → IsNowhereDense tᶜ := fun t ht ↦ (this t ht).2
    -- Thus (s'')ᶜ =s is meagre.
    rw [IsMeagre]
    use compl '' s'
    constructor
    · rintro t ⟨x, hx, hcompl⟩
      rw [← hcompl]
      exact this x hx
    · constructor
      · exact Countable.image hcountable _
      · apply h

/-- The empty set is meagre. -/
lemma meagre_empty : IsMeagre (∅ : Set α) := by
  rw [meagre_iff_complement_comeagre, compl_empty, ← Filter.eventuallyEq_univ]

/-- Subsets of meagre sets are meagre. -/
lemma meagre_mono {s t: Set α} (hs : IsMeagre s) (hts: t ⊆ s) : IsMeagre t := by
  rw [← compl_subset_compl] at hts
  rw [meagre_iff_complement_comeagre] at *
  exact Filter.mem_of_superset hs hts

/-- A finite intersection of meagre sets is meagre. -/
-- xxx is this superfluous? I presume it is?
lemma meagre_inter {s t : Set α} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  meagre_mono hs (inter_subset_left s t)

/-- A countable union of meagre sets is meagre. -/
lemma meagre_iUnion {s : ℕ → Set α} (hs : ∀ n : ℕ, IsMeagre (s n)) :
    IsMeagre (⋃ (n : ℕ), (s n)) := by
  simp only [meagre_iff_complement_comeagre, compl_iUnion] at *
  exact Iff.mpr countable_iInter_mem hs
