/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module topology.G_delta
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Separation

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the filter of residual sets. A set `s` is called *residual* if it includes a dense
  `Gδ` set. In a Baire space (e.g., in a complete (e)metric space), residual sets form a filter.

  For technical reasons, we define `residual` in any topological space but the definition agrees
  with the description above only in Baire spaces.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/


noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {α β γ ι : Type _}

set_option linter.uppercaseLean3 false

section IsGδ

variable [TopologicalSpace α]

/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set α) : Prop :=
  ∃ T : Set (Set α), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
#align is_Gδ IsGδ

/-- An open set is a Gδ set. -/
theorem IsOpen.isGδ {s : Set α} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩
#align is_open.is_Gδ IsOpen.isGδ

@[simp]
theorem isGδ_empty : IsGδ (∅ : Set α) :=
  isOpen_empty.isGδ
#align is_Gδ_empty isGδ_empty

@[simp]
theorem isGδ_univ : IsGδ (univ : Set α) :=
  isOpen_univ.isGδ
#align is_Gδ_univ isGδ_univ

theorem isGδ_biInter_of_open {I : Set ι} (hI : I.Countable) {f : ι → Set α}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [ball_image_iff], hI.image _, by rw [sInter_image]⟩
#align is_Gδ_bInter_of_open isGδ_biInter_of_open

-- porting note: TODO: generalize to `Sort _` + `Countable _`
theorem isGδ_iInter_of_open [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
#align is_Gδ_Inter_of_open isGδ_iInter_of_open

-- porting note: TODO: generalize to `Sort _` + `Countable _`
/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
theorem isGδ_iInter [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsGδ (s i)) : IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine' ⟨⋃ i, T i, _, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_swap ι] using hTo
#align is_Gδ_Inter isGδ_iInter

theorem isGδ_biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set α}
    (ht : ∀ (i) (hi : i ∈ s), IsGδ (t i hi)) : IsGδ (⋂ i ∈ s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  haveI := hs.toEncodable
  exact isGδ_iInter fun x => ht x x.2
#align is_Gδ_bInter isGδ_biInter

/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem isGδ_sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using isGδ_biInter hS h
#align is_Gδ_sInter isGδ_sInter

theorem IsGδ.inter {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact isGδ_iInter (Bool.forall_bool.2 ⟨ht, hs⟩)
#align is_Gδ.inter IsGδ.inter

/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  apply isGδ_biInter_of_open (Scount.prod Tcount)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)
#align is_Gδ.union IsGδ.union

-- porting note: TODO: add `iUnion` and `sUnion` versions
/-- The union of finitely many Gδ sets is a Gδ set. -/
theorem isGδ_biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set α} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  refine' Finite.induction_on hs (by simp) _ h
  simp only [ball_insert_iff, biUnion_insert]
  exact fun _ _ ihs H => H.1.union (ihs H.2)
#align is_Gδ_bUnion isGδ_biUnion

-- Porting note: Did not recognize notation 𝓤 α, needed to replace with uniformity α
theorem IsClosed.isGδ {α} [UniformSpace α] [IsCountablyGenerated (uniformity α)] {s : Set α}
    (hs : IsClosed s) : IsGδ s := by
  rcases(@uniformity_hasBasis_open α _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  rw [← hs.closure_eq, ← hU.biInter_biUnion_ball]
  refine' isGδ_biInter (to_countable _) fun n _ => IsOpen.isGδ _
  exact isOpen_biUnion fun x _ => UniformSpace.isOpen_ball _ (hUo _).2
#align is_closed.is_Gδ IsClosed.isGδ

section T1Space

variable [T1Space α]

theorem isGδ_compl_singleton (a : α) : IsGδ ({a}ᶜ : Set α) :=
  isOpen_compl_singleton.isGδ
#align is_Gδ_compl_singleton isGδ_compl_singleton

theorem Set.Countable.isGδ_compl {s : Set α} (hs : s.Countable) : IsGδ (sᶜ) := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  exact isGδ_biInter hs fun x _ => isGδ_compl_singleton x
#align set.countable.is_Gδ_compl Set.Countable.isGδ_compl

theorem Set.Finite.isGδ_compl {s : Set α} (hs : s.Finite) : IsGδ (sᶜ) :=
  hs.countable.isGδ_compl
#align set.finite.is_Gδ_compl Set.Finite.isGδ_compl

theorem Set.Subsingleton.isGδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ (sᶜ) :=
  hs.finite.isGδ_compl
#align set.subsingleton.is_Gδ_compl Set.Subsingleton.isGδ_compl

theorem Finset.isGδ_compl (s : Finset α) : IsGδ (sᶜ : Set α) :=
  s.finite_toSet.isGδ_compl
#align finset.is_Gδ_compl Finset.isGδ_compl

variable [FirstCountableTopology α]

theorem isGδ_singleton (a : α) : IsGδ ({a} : Set α) := by
  rcases (nhds_basis_opens a).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact isGδ_biInter (to_countable _) fun n _ => (hU n).2.isGδ
#align is_Gδ_singleton isGδ_singleton

theorem Set.Finite.isGδ {s : Set α} (hs : s.Finite) : IsGδ s :=
  Finite.induction_on hs isGδ_empty fun _ _ hs => (isGδ_singleton _).union hs
#align set.finite.is_Gδ Set.Finite.isGδ

end T1Space

end IsGδ

section ContinuousAt

variable [TopologicalSpace α]

/-- The set of points where a function is continuous is a Gδ set. -/
theorem isGδ_setOf_continuousAt [UniformSpace β] [IsCountablyGenerated (uniformity β)] (f : α → β) :
    IsGδ { x | ContinuousAt f x } := by
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric β _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis, forall_prop_of_true,
    setOf_forall, id]
  refine' isGδ_iInter fun k => IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x => _
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx]with _ hy using⟨s, ⟨hy, hso⟩, hsU⟩
#align is_Gδ_set_of_continuous_at isGδ_setOf_continuousAt

end ContinuousAt

/-- A set `s` is called *residual* if it includes a dense `Gδ` set. If `α` is a Baire space
(e.g., a complete metric space), then residual sets form a filter, see `mem_residual`.

For technical reasons we define the filter `residual` in any topological space but in a non-Baire
space it is not useful because it may contain some non-residual sets. -/
def residual (α : Type _) [TopologicalSpace α] : Filter α :=
  ⨅ (t) (_ht : IsGδ t) (_ht' : Dense t), 𝓟 t
#align residual residual
