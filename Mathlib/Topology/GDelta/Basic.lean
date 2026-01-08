/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Data.Set.Notation
import Mathlib.Topology.Constructions

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

We prove that finite or countable intersections of Gδ sets are Gδ sets.

- `isClosed_isNowhereDense_iff_compl`: a closed set is nowhere dense iff
its complement is open and dense
- `isMeagre_iff_countable_union_isNowhereDense`: a set is meagre iff it is contained in a countable
union of nowhere dense sets
- subsets of meagre sets are meagre; countable unions of meagre sets are meagre

See `Mathlib/Topology/GDelta/MetrizableSpace.lean` for the proof that
continuity set of a function from a topological space to a metrizable space is a Gδ set.

## Tags

Gδ set, residual set, nowhere dense set, meagre set
-/

@[expose] public section

assert_not_exists UniformSpace

noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {X Y ι : Type*} {ι' : Sort*}


section IsGδ

variable [TopologicalSpace X]

/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

/-- An open set is a Gδ set. -/
theorem IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩

@[simp]
protected theorem IsGδ.empty : IsGδ (∅ : Set X) :=
  isOpen_empty.isGδ


@[simp]
protected theorem IsGδ.univ : IsGδ (univ : Set X) :=
  isOpen_univ.isGδ


theorem IsGδ.biInter_of_isOpen {I : Set ι} (hI : I.Countable) {f : ι → Set X}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩


theorem IsGδ.iInter_of_isOpen [Countable ι'] {f : ι' → Set X} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩


lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n ↦ univ, fun _n ↦ isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf

alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat

/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
protected theorem IsGδ.iInter [Countable ι'] {s : ι' → Set X} (hs : ∀ i, IsGδ (s i)) :
    IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_swap ι'] using hTo

theorem IsGδ.biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set X}
    (ht : ∀ (i) (hi : i ∈ s), IsGδ (t i hi)) : IsGδ (⋂ i ∈ s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  haveI := hs.to_subtype
  exact .iInter fun x => ht x x.2


/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem IsGδ.sInter {S : Set (Set X)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h


theorem IsGδ.inter {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)

/-- The union of finitely many Gδ sets is a Gδ set, `Set.sUnion` version. -/
theorem IsGδ.sUnion {S : Set (Set X)} (hS : S.Finite) (h : ∀ s ∈ S, IsGδ s) : IsGδ (⋃₀ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)

/-- The union of finitely many Gδ sets is a Gδ set, bounded indexed union version. -/
theorem IsGδ.biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set X} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)

/-- The union of finitely many Gδ sets is a Gδ set, bounded indexed union version. -/
theorem IsGδ.iUnion [Finite ι'] {f : ι' → Set X} (h : ∀ i, IsGδ (f i)) : IsGδ (⋃ i, f i) :=
  .sUnion (finite_range _) <| forall_mem_range.2 h

end IsGδ

section residual

variable [TopologicalSpace X]

/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }

instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance

/-- Dense open sets are residual. -/
theorem residual_of_dense_open {s : Set X} (ho : IsOpen s) (hd : Dense s) : s ∈ residual X :=
  CountableGenerateSets.basic ⟨ho, hd⟩

/-- Dense Gδ sets are residual. -/
theorem residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd : Dense s) : s ∈ residual X := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))

/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set X} :
    s ∈ residual X ↔
      ∃ S : Set (Set X), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_setOf, forall_and, and_assoc]

end residual

section IsMeagre
open Function TopologicalSpace Set
variable [TopologicalSpace X]

/-- A set is called **nowhere dense** iff its closure has empty interior. -/
def IsNowhereDense (s : Set X) := interior (closure s) = ∅

/-- The empty set is nowhere dense. -/
@[simp]
lemma isNowhereDense_empty : IsNowhereDense (∅ : Set X) := by
  rw [IsNowhereDense, closure_empty, interior_empty]

/-- A subset of a nowhere dense set is nowhere dense. -/
@[gcongr]
lemma IsNowhereDense.mono {s t : Set X} (ht : t ⊆ s) (hs : IsNowhereDense s) : IsNowhereDense t :=
  Set.eq_empty_of_subset_empty <| by grw [ht]; rw [hs]

/-- A closed set is nowhere dense iff its interior is empty. -/
lemma IsClosed.isNowhereDense_iff {s : Set X} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]

/-- If a set `s` is nowhere dense, so is its closure. -/
protected lemma IsNowhereDense.closure {s : Set X} (hs : IsNowhereDense s) :
    IsNowhereDense (closure s) := by
  rwa [IsNowhereDense, closure_closure]

/-- A nowhere dense set `s` is contained in a closed nowhere dense set (namely, its closure). -/
lemma IsNowhereDense.subset_of_closed_isNowhereDense {s : Set X} (hs : IsNowhereDense s) :
    ∃ t : Set X, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t :=
  ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩

/-- A set `s` is closed and nowhere dense iff its complement `sᶜ` is open and dense. -/
lemma isClosed_isNowhereDense_iff_compl {s : Set X} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  rw [and_congr_right IsClosed.isNowhereDense_iff,
    isOpen_compl_iff, interior_eq_empty_iff_dense_compl]

/-- The image of a nowhere dense set through an inducing map is nowhere dense. -/
lemma Topology.IsInducing.isNowhereDense_image [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsInducing f) {s : Set X} (h : IsNowhereDense s) : IsNowhereDense (f '' s) := by
  rw [IsNowhereDense.eq_1] at *
  contrapose! h
  rw [hf.closure_eq_preimage_closure_image]
  obtain ⟨y, o, ⟨isOpen_o, ho⟩, y_mem_o⟩ := h
  obtain ⟨_, hx, x, x_mem_s, rfl⟩ := mem_closure_iff.mp (ho y_mem_o) o isOpen_o y_mem_o
  refine ⟨x, f⁻¹' o, ⟨hf.continuous.isOpen_preimage o isOpen_o, by grw [ho]⟩, hx⟩

/-- A set is nowhere dense if it is nowhere dense in some subspace. -/
lemma IsNowhereDense.image_val {Y : Set X} {s : Set Y}
    (hs : IsNowhereDense s) : IsNowhereDense (s : Set X) :=
  Topology.IsInducing.subtypeVal.isNowhereDense_image hs

/-- A set is called **meagre** iff its complement is a residual (or comeagre) set. -/
def IsMeagre (s : Set X) := sᶜ ∈ residual X

/-- The empty set is meagre. -/
lemma IsMeagre.empty : IsMeagre (∅ : Set X) := by
  rw [IsMeagre, compl_empty]
  exact Filter.univ_mem

/-- Subsets of meagre sets are meagre. -/
@[gcongr]
lemma IsMeagre.mono {s t : Set X} (hts : t ⊆ s) (hs : IsMeagre s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

/-- An intersection with a meagre set is meagre. -/
lemma IsMeagre.inter {s t : Set X} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  hs.mono inter_subset_left

/-- A union of two meagre sets is meagre. -/
lemma IsMeagre.union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s ∪ t) := by
  rw [IsMeagre, compl_union]
  exact inter_mem hs ht

/-- A countable union of meagre sets is meagre. -/
lemma isMeagre_iUnion [Countable ι'] {f : ι' → Set X} (hs : ∀ i, IsMeagre (f i)) :
    IsMeagre (⋃ i, f i) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs

/-- A set is meagre iff it is contained in a countable union of nowhere dense sets. -/
lemma isMeagre_iff_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  rw [IsMeagre, mem_residual_iff, compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS, hc, hsub⟩ ↦ ⟨S, fun s hs ↦ (hS hs).2, ?_, hsub⟩, ?_⟩
  · rw [← compl_compl_image S]; exact hc.image _
  · intro ⟨S, hS, hc, hsub⟩
    use closure '' S
    rw [forall_mem_image]
    exact ⟨fun s hs ↦ ⟨isClosed_closure, (hS s hs).closure⟩,
      (hc.image _).image _, hsub.trans (sUnion_mono_subsets fun s ↦ subset_closure)⟩

/-- A set of second category (i.e. non-meagre) is nonempty. -/
lemma nonempty_of_not_isMeagre {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using IsMeagre.empty

/-- A nowhere dense set is meagre. -/
lemma IsNowhereDense.isMeagre {s : Set X} (h : IsNowhereDense s) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa, by simp, by simp⟩

lemma exists_of_not_isMeagre_biUnion {I : Set ι}
    (c : I.Countable) {A : ι → Set X} (h : ¬IsMeagre (⋃ i ∈ I, A i)) :
    ∃ i ∈ I, ¬IsMeagre (A i) := by
  contrapose! h
  suffices IsMeagre (⋃ i : I, A i) by
    convert this
    simp
  have : Countable I := c
  apply isMeagre_iUnion
  intro ⟨i, hi⟩
  exact h i hi

/-- The image of a meagre set through an inducing map is meagre. -/
lemma Topology.IsInducing.isMeagre_image {f : X → Y} [TopologicalSpace Y]
    (hf : Topology.IsInducing f) {s : Set X} (h : IsMeagre s) : IsMeagre (f '' s) := by
  rw [isMeagre_iff_countable_union_isNowhereDense] at *
  obtain ⟨T, isNowhereDense, countable, cover⟩ := h
  refine ⟨(Set.image f) '' T, ?isNowhereDense, countable.image _, ?cover⟩
  case isNowhereDense =>
    intro u ⟨t, tT, tu⟩
    rw [← tu]
    apply hf.isNowhereDense_image (isNowhereDense t tT)
  case cover =>
    rw [← Set.image_sUnion]
    grw [cover]

/-- A set is meagre if it is meagre in some subspace. -/
lemma IsMeagre.image_val {s : Set X} {m : Set s} (h : IsMeagre (m : Set s)) :
    IsMeagre (m : Set X) := Topology.IsInducing.subtypeVal.isMeagre_image h

end IsMeagre
