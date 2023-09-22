/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Topology.GDelta

/-!
## Nowhere dense and meagre sets
Define nowhere dense and meagre sets (`IsNowhereDense` and `IsMeagre`, respectively)
as complements of open dense and residual sets, respectively, and prove their basic properties.

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
def IsNowhereDense (s : Set α) := interior (closure s) = ∅

/-- A closed set is nowhere dense iff its interior is empty. -/
lemma closed_nowhere_dense_iff {s : Set α} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
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
      exact hNowhereDense
  · rintro ⟨hopen, hdense⟩
    constructor
    · exact { isOpen_compl := hopen }
    · have : IsClosed s := by exact { isOpen_compl := hopen }
      rw [closed_nowhere_dense_iff this, interior_eq_empty_iff_dense_compl]
      exact hdense

/-- A set is **meagre** iff its complement is a residual (or comeagre) set. -/
def IsMeagre (s : Set α) := sᶜ ∈ residual α

/-- The empty set is meagre. -/
lemma meagre_empty : IsMeagre (∅ : Set α) := by
  rw [IsMeagre, compl_empty]
  exact Filter.univ_mem

/-- Subsets of meagre sets are meagre. -/
lemma IsMeagre.mono {s t: Set α} (hs : IsMeagre s) (hts: t ⊆ s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

/-- A finite intersection of meagre sets is meagre. -/
-- xxx is this superfluous?
lemma IsMeagre.inter {s t : Set α} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  hs.mono (inter_subset_left s t)

/-- A countable union of meagre sets is meagre. -/
lemma meagre_iUnion {s : ℕ → Set α} (hs : ∀ n, IsMeagre (s n)) : IsMeagre (⋃ n, (s n)) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

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

/-- A set is meagre iff it is contained in the countable union of nowhere dense sets. -/
lemma meagre_iff_countable_union_nowhere_dense {s : Set α} : IsMeagre s ↔
    ∃ S : Set (Set α), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  constructor
  · intro hs -- suppose s is meagre, i.e. sᶜ is residual
    rw [IsMeagre, mem_residual_iff] at hs
    rcases hs with ⟨s', ⟨hopen, hdense, hcountable, hss'⟩⟩
    have h : s ⊆ ⋃₀ (compl '' s') := calc
      s = sᶜᶜ := by rw [compl_compl s]
      _ ⊆ (⋂₀ s')ᶜ := Iff.mpr compl_subset_compl hss'
      _ = ⋃₀ (compl '' s') := by rw [compl_sInter]
    -- Each u_iᶜ is closed and nowhere dense, hence nowhere dense. Thus, (s'')ᶜ =s is meagre.
    use compl '' s'
    constructor
    · rintro t ⟨x, hx, hcompl⟩
      rw [← hcompl]
      have : IsOpen xᶜᶜ ∧ Dense xᶜᶜ := by
        rw [compl_compl]
        exact ⟨hopen x hx, hdense x hx⟩
      exact (closed_nowhere_dense_iff_complement.mpr this).2
    · exact ⟨Countable.image hcountable _, h⟩
  · -- Assume `s` is the countable union of nowhere dense sets s_i.
    rintro ⟨s', ⟨hnowhereDense, hcountable, hss'⟩⟩
    rw [IsMeagre, mem_residual_iff]
    -- Passing to the closure, assume all s_i are closed nowhere dense.
    let s'' := closure '' s'
    -- Then each s_iᶜ is open and dense.
    let complement := compl '' s''
    have hnowhereDense' : ∀ (t : Set α), t ∈ s'' → IsClosed t ∧ IsNowhereDense t := by
      rintro t ⟨x, hx, hclosed⟩
      rw [← hclosed]
      exact ⟨isClosed_closure, closure_nowhere_dense (hnowhereDense x hx)⟩
    have h' : ∀ (t : Set α), t ∈ complement → IsOpen t ∧ Dense t := by
      rintro t ⟨x, hx, hcompl⟩
      rw [← hcompl]
      exact closed_nowhere_dense_iff_complement.mp (hnowhereDense' x hx)
    -- and we compute ⋂ U_iᶜ ⊆ sᶜ, completing the proof.
    have hss'' : s ⊆ ⋃₀ s'' := calc
      s ⊆ ⋃₀ s' := hss'
      _ ⊆ ⋃₀ s'' := sUnion_subset_closure
    have h₂: ⋂₀ complement ⊆ sᶜ := calc ⋂₀ complement
      _ = (⋃₀ s'')ᶜ := by rw [←compl_sUnion]
      _ ⊆ sᶜ := compl_subset_compl.mpr hss''
    use complement
    exact ⟨fun t ht ↦ (h' t ht).1, fun t ht ↦(h' t ht).2,
           Countable.image (Countable.image hcountable _) compl, h₂⟩
