/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.CountableInter

#align_import topology.G_delta from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

* `IsNowhereDense`: a set is called *nowhere dense* iff its closure has empty interior
* `IsMeagre`: a set `s` is called *meagre* iff its complement is residual

## Main results

We prove that finite or countable intersections of Gδ sets are a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

- `closed_nowhere_dense_iff_complement`: a closed set is nowhere dense iff
its complement is open and dense
- `meagre_iff_countable_union_nowhere_dense`: a set is meagre iff it is contained in the countable
union of open and dense sets
- subsets of meagre sets are meagre; countable unions of meagre sets are meagre

## Tags

Gδ set, residual set, nowhere dense set, meagre set
-/


noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {α β γ ι : Type*}

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

-- porting note: TODO: generalize to `Sort*` + `Countable _`
theorem isGδ_iInter_of_open [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
#align is_Gδ_Inter_of_open isGδ_iInter_of_open

-- porting note: TODO: generalize to `Sort*` + `Countable _`
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

theorem Set.Countable.isGδ_compl {s : Set α} (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  exact isGδ_biInter hs fun x _ => isGδ_compl_singleton x
#align set.countable.is_Gδ_compl Set.Countable.isGδ_compl

theorem Set.Finite.isGδ_compl {s : Set α} (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl
#align set.finite.is_Gδ_compl Set.Finite.isGδ_compl

theorem Set.Subsingleton.isGδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ sᶜ :=
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

section residual

variable [TopologicalSpace α]

/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (α : Type*) [TopologicalSpace α] : Filter α :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
#align residual residual

instance countableInterFilter_residual : CountableInterFilter (residual α) := by
  rw [residual]; infer_instance
#align countable_Inter_filter_residual countableInterFilter_residual

/-- Dense open sets are residual. -/
theorem residual_of_dense_open {s : Set α} (ho : IsOpen s) (hd : Dense s) : s ∈ residual α :=
  CountableGenerateSets.basic ⟨ho, hd⟩
#align residual_of_dense_open residual_of_dense_open

/-- Dense Gδ sets are residual. -/
theorem residual_of_dense_Gδ {s : Set α} (ho : IsGδ s) (hd : Dense s) : s ∈ residual α := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))
#align residual_of_dense_Gδ residual_of_dense_Gδ

/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set α} :
    s ∈ residual α ↔
      ∃ S : Set (Set α), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_setOf, forall_and, and_assoc]
#align mem_residual_iff mem_residual_iff

end residual

section meagre
open Function TopologicalSpace Set
variable {α : Type*} [TopologicalSpace α]

/-- A set is called **nowhere dense** iff its closure has empty interior. -/
def IsNowhereDense (s : Set α) := interior (closure s) = ∅

/-- The empty set is nowhere dense. -/
@[simp]
lemma isNowhereDense_of_empty : IsNowhereDense (∅ : Set α) := by
  unfold IsNowhereDense
  rw [closure_empty, interior_empty]

/-- A closed set is nowhere dense iff its interior is empty. -/
lemma IsClosed.nowhere_dense_iff {s : Set α} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]

/-- If a set `s` is nowhere dense, so is its closure.-/
lemma IsNowhereDense.closure_nowhere_dense {s : Set α} (hs : IsNowhereDense s) :
    IsNowhereDense (closure s) := by
  rw [IsNowhereDense, closure_closure]
  exact hs

/-- A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its closure). -/
lemma IsNowhereDense.subset_of_closed_nowhere_dense {s : Set α} (hs : IsNowhereDense s) :
    ∃ t : Set α, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t :=
  ⟨closure s, subset_closure, ⟨hs.closure_nowhere_dense, isClosed_closure⟩⟩

/-- A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense. -/
lemma closed_nowhere_dense_iff_complement {s : Set α} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  constructor
  · rintro ⟨hclosed, hNowhereDense⟩
    rw [hclosed.nowhere_dense_iff] at hNowhereDense
    exact ⟨isOpen_compl_iff.mpr hclosed, interior_eq_empty_iff_dense_compl.mp hNowhereDense⟩
  · rintro ⟨hopen, hdense⟩
    constructor
    · exact { isOpen_compl := hopen }
    · have : IsClosed s := by exact { isOpen_compl := hopen }
      rw [this.nowhere_dense_iff, interior_eq_empty_iff_dense_compl]
      exact hdense

/-- A set is called **meagre** iff its complement is a residual (or comeagre) set. -/
def IsMeagre (s : Set α) := sᶜ ∈ residual α

/-- The empty set is meagre. -/
lemma meagre_empty : IsMeagre (∅ : Set α) := by
  rw [IsMeagre, compl_empty]
  exact Filter.univ_mem

/-- Subsets of meagre sets are meagre. -/
lemma IsMeagre.mono {s t: Set α} (hs : IsMeagre s) (hts: t ⊆ s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

/-- A finite intersection of meagre sets is meagre. -/
lemma IsMeagre.inter {s t : Set α} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  hs.mono (inter_subset_left s t)

/-- A countable union of meagre sets is meagre. -/
lemma meagre_iUnion {s : ℕ → Set α} (hs : ∀ n, IsMeagre (s n)) : IsMeagre (⋃ n, (s n)) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

/-- A set is meagre iff it is contained in the countable union of nowhere dense sets. -/
lemma meagre_iff_countable_union_nowhere_dense {s : Set α} : IsMeagre s ↔
    ∃ S : Set (Set α), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  constructor
  · intro hs -- suppose s is meagre, i.e. sᶜ is residual
    rw [IsMeagre, mem_residual_iff] at hs
    rcases hs with ⟨s', ⟨hopen, hdense, hcountable, hss'⟩⟩
    have h : s ⊆ ⋃₀ (compl '' s') := calc
      s = sᶜᶜ := by rw [compl_compl s]
      _ ⊆ (⋂₀ s')ᶜ := compl_subset_compl.mpr hss'
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
      exact ⟨isClosed_closure, (hnowhereDense x hx).closure_nowhere_dense⟩
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
end meagre
