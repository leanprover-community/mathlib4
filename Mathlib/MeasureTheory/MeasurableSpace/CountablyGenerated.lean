/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher, Yury G. Kudryashov, Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.MemPartition
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Countably generated measurable spaces

We say a measurable space is countably generated if it can be generated by a countable set of sets.

In such a space, we can also build a sequence of finer and finer finite measurable partitions of
the space such that the measurable space is generated by the union of all partitions.

## Main definitions

* `MeasurableSpace.CountablyGenerated`: class stating that a measurable space is countably
  generated.
* `MeasurableSpace.countablePartition`: sequences of finer and finer partitions of
  a countably generated space.
* `MeasurableSpace.partitionSet`: `partitionSet n t` is the set in the partition
  `countablePartition α n` to which `t` belongs.

## Main statements

* `MeasurableSpace.measurable_injection_nat_bool_of_countablyGenerated`: if a measurable space is
  countably generated and separates points, it admits a measurable injection into the Cantor space
  `ℕ → Bool` (equipped with the product sigma algebra).

-/


open Set MeasureTheory

namespace MeasurableSpace

variable {α β : Type*}

/-- We say a measurable space is countably generated
if it can be generated by a countable set of sets. -/
class CountablyGenerated (α : Type*) [m : MeasurableSpace α] : Prop where
  isCountablyGenerated : ∃ b : Set (Set α), b.Countable ∧ m = generateFrom b
#align measurable_space.countably_generated MeasurableSpace.CountablyGenerated

/-- A countable set of sets that generate the measurable space.
We insert `∅` to ensure it is nonempty. -/
def countableGeneratingSet (α : Type*) [MeasurableSpace α] [h : CountablyGenerated α] :
    Set (Set α) :=
  insert ∅ h.isCountablyGenerated.choose

lemma countable_countableGeneratingSet [MeasurableSpace α] [h : CountablyGenerated α] :
    Countable (countableGeneratingSet α) :=
  Countable.insert _ h.isCountablyGenerated.choose_spec.1

lemma generateFrom_countableGeneratingSet [m : MeasurableSpace α] [h : CountablyGenerated α] :
    generateFrom (countableGeneratingSet α) = m :=
  (generateFrom_insert_empty _).trans <| h.isCountablyGenerated.choose_spec.2.symm

lemma empty_mem_countableGeneratingSet [MeasurableSpace α] [CountablyGenerated α] :
    ∅ ∈ countableGeneratingSet α := mem_insert _ _

lemma nonempty_countableGeneratingSet [MeasurableSpace α] [CountablyGenerated α] :
    Set.Nonempty (countableGeneratingSet α) :=
  ⟨∅, mem_insert _ _⟩

theorem CountablyGenerated.comap [m : MeasurableSpace β] [h : CountablyGenerated β] (f : α → β) :
    @CountablyGenerated α (.comap f m) := by
  rcases h with ⟨⟨b, hbc, rfl⟩⟩
  rw [comap_generateFrom]
  letI := generateFrom (preimage f '' b)
  exact ⟨_, hbc.image _, rfl⟩

theorem CountablyGenerated.sup {m₁ m₂ : MeasurableSpace β} (h₁ : @CountablyGenerated β m₁)
    (h₂ : @CountablyGenerated β m₂) : @CountablyGenerated β (m₁ ⊔ m₂) := by
  rcases h₁ with ⟨⟨b₁, hb₁c, rfl⟩⟩
  rcases h₂ with ⟨⟨b₂, hb₂c, rfl⟩⟩
  exact @mk _ (_ ⊔ _) ⟨_, hb₁c.union hb₂c, generateFrom_sup_generateFrom⟩

instance (priority := 100) [MeasurableSpace α] [Finite α] : CountablyGenerated α where
  isCountablyGenerated :=
    ⟨{s | MeasurableSet s}, Set.to_countable _, generateFrom_measurableSet.symm⟩

instance [MeasurableSpace α] [CountablyGenerated α] {p : α → Prop} :
    CountablyGenerated { x // p x } := .comap _

instance [MeasurableSpace α] [CountablyGenerated α] [MeasurableSpace β] [CountablyGenerated β] :
    CountablyGenerated (α × β) :=
  .sup (.comap Prod.fst) (.comap Prod.snd)

instance [MeasurableSpace α] {s : Set α} [h : CountablyGenerated s] [MeasurableSingletonClass s] :
    HasCountableSeparatingOn α MeasurableSet s := by
  suffices HasCountableSeparatingOn s MeasurableSet univ from this.of_subtype fun _ ↦ id
  rcases h.1 with ⟨b, hbc, hb⟩
  refine ⟨⟨b, hbc, fun t ht ↦ hb.symm ▸ .basic t ht, fun x _ y _ h ↦ ?_⟩⟩
  rw [← forall_generateFrom_mem_iff_mem_iff, ← hb] at h
  simpa using h {y}

section MeasurableMemPartition

lemma measurableSet_succ_memPartition (t : ℕ → Set α) (n : ℕ) {s : Set α}
    (hs : s ∈ memPartition t n) :
    MeasurableSet[generateFrom (memPartition t (n + 1))] s := by
  rw [← diff_union_inter s (t n)]
  refine MeasurableSet.union ?_ ?_ <;>
    · refine measurableSet_generateFrom ?_
      rw [memPartition_succ]
      exact ⟨s, hs, by simp⟩

lemma generateFrom_memPartition_le_succ (t : ℕ → Set α) (n : ℕ) :
    generateFrom (memPartition t n) ≤ generateFrom (memPartition t (n + 1)) :=
  generateFrom_le (fun _ hs ↦ measurableSet_succ_memPartition t n hs)

lemma measurableSet_generateFrom_memPartition (t : ℕ → Set α) (n : ℕ) :
    MeasurableSet[generateFrom (memPartition t (n + 1))] (t n) := by
  have : t n = ⋃ u ∈ memPartition t n, u ∩ t n := by
    simp_rw [← iUnion_inter, ← sUnion_eq_biUnion, sUnion_memPartition, univ_inter]
  rw [this]
  refine MeasurableSet.biUnion (finite_memPartition _ _).countable (fun v hv ↦ ?_)
  refine measurableSet_generateFrom ?_
  rw [memPartition_succ]
  exact ⟨v, hv, Or.inl rfl⟩

lemma generateFrom_iUnion_memPartition (t : ℕ → Set α) :
    generateFrom (⋃ n, memPartition t n) = generateFrom (range t) := by
  refine le_antisymm (generateFrom_le fun u hu ↦ ?_) (generateFrom_le fun u hu ↦ ?_)
  · simp only [mem_iUnion] at hu
    obtain ⟨n, hun⟩ := hu
    induction n generalizing u with
    | zero =>
      simp only [Nat.zero_eq, memPartition_zero, mem_insert_iff, mem_singleton_iff] at hun
      rw [hun]
      exact MeasurableSet.univ
    | succ n ih =>
      simp only [memPartition_succ, mem_setOf_eq] at hun
      obtain ⟨v, hv, huv⟩ := hun
      rcases huv with rfl | rfl
      · exact (ih v hv).inter (measurableSet_generateFrom ⟨n, rfl⟩)
      · exact (ih v hv).diff (measurableSet_generateFrom ⟨n, rfl⟩)
  · simp only [iUnion_singleton_eq_range, mem_range] at hu
    obtain ⟨n, rfl⟩ := hu
    exact generateFrom_mono (subset_iUnion _ _) _ (measurableSet_generateFrom_memPartition t n)

lemma generateFrom_memPartition_le (t : ℕ → Set α) (n : ℕ) :
    generateFrom (memPartition t n) ≤ generateFrom (range t) := by
  conv_rhs => rw [← generateFrom_iUnion_memPartition t]
  exact generateFrom_mono (subset_iUnion _ _)

end MeasurableMemPartition

variable [m : MeasurableSpace α] [h : CountablyGenerated α]

/-- For each `n : ℕ`, `countablePartition α n` is a partition of the space in at most
`2^(n+1)` sets. Each partition is finer than the preceeding one. The measurable space generated by
the union of all those partions is the measurable space on `α`. -/
def countablePartition (α : Type*) [MeasurableSpace α] [CountablyGenerated α] : ℕ → Set (Set α) :=
  memPartition (enumerateCountable countable_countableGeneratingSet ∅)

lemma finite_countablePartition (α : Type*) [MeasurableSpace α] [CountablyGenerated α] (n : ℕ) :
    Set.Finite (countablePartition α n) :=
  finite_memPartition _ n

instance instFinite_countablePartition (n : ℕ) : Finite (countablePartition α n) :=
  Set.finite_coe_iff.mp (finite_countablePartition _ _)

lemma disjoint_countablePartition {n : ℕ} {s t : Set α}
    (hs : s ∈ countablePartition α n) (ht : t ∈ countablePartition α n) (hst : s ≠ t) :
    Disjoint s t :=
  disjoint_memPartition _ n hs ht hst

lemma sUnion_countablePartition (α : Type*) [MeasurableSpace α] [CountablyGenerated α] (n : ℕ) :
    ⋃₀ countablePartition α n = univ :=
  sUnion_memPartition _ n

lemma measurableSet_succ_countablePartition (n : ℕ) {s : Set α} (hs : s ∈ countablePartition α n) :
    MeasurableSet[generateFrom (countablePartition α (n + 1))] s :=
  measurableSet_succ_memPartition _ _ hs

lemma generateFrom_countablePartition_le_succ (α : Type*) [MeasurableSpace α] [CountablyGenerated α]
    (n : ℕ) :
    generateFrom (countablePartition α n) ≤ generateFrom (countablePartition α (n + 1)) :=
  generateFrom_memPartition_le_succ _ _

lemma generateFrom_iUnion_countablePartition (α : Type*) [m : MeasurableSpace α]
    [CountablyGenerated α] :
    generateFrom (⋃ n, countablePartition α n) = m := by
  conv_rhs => rw [← generateFrom_countableGeneratingSet (α := α)]
  convert generateFrom_iUnion_memPartition _
  rw [range_enumerateCountable_of_mem _ empty_mem_countableGeneratingSet]

lemma generateFrom_countablePartition_le (α : Type*) [m : MeasurableSpace α] [CountablyGenerated α]
    (n : ℕ) :
    generateFrom (countablePartition α n) ≤ m := by
  conv_rhs => rw [← generateFrom_iUnion_countablePartition α]
  exact generateFrom_mono (subset_iUnion _ _)

lemma measurableSet_countablePartition (n : ℕ) {s : Set α} (hs : s ∈ countablePartition α n) :
    MeasurableSet s :=
  generateFrom_countablePartition_le α n _ (measurableSet_generateFrom hs)

/-- The set in `countablePartition α n` to which `a : α` belongs. -/
def countablePartitionSet (n : ℕ) (a : α) : Set α :=
  memPartitionSet (enumerateCountable countable_countableGeneratingSet ∅) n a
  --(exists_countablePartition_mem n a).choose

lemma countablePartitionSet_mem (n : ℕ) (a : α) :
    countablePartitionSet n a ∈ countablePartition α n :=
  memPartitionSet_mem _ _ _

lemma mem_countablePartitionSet (n : ℕ) (a : α) : a ∈ countablePartitionSet n a :=
  mem_memPartitionSet _ _ _

lemma countablePartitionSet_eq_iff {n : ℕ} (a : α) {s : Set α} (hs : s ∈ countablePartition α n) :
    countablePartitionSet n a = s ↔ a ∈ s :=
  memPartitionSet_eq_iff _ hs

lemma countablePartitionSet_of_mem {n : ℕ} {a : α} {s : Set α} (hs : s ∈ countablePartition α n)
    (ha : a ∈ s) :
    countablePartitionSet n a = s :=
  memPartitionSet_of_mem hs ha

lemma measurableSet_countablePartitionSet (n : ℕ) (a : α) :
    MeasurableSet (countablePartitionSet n a) :=
  measurableSet_countablePartition n (countablePartitionSet_mem n a)

variable (α)

open Classical

/-- If a measurable space is countably generated and separates points, it admits a measurable
injection into the Cantor space `ℕ → Bool` (equipped with the product sigma algebra). -/
theorem measurable_injection_nat_bool_of_countablyGenerated [MeasurableSpace α]
    [HasCountableSeparatingOn α MeasurableSet univ] :
    ∃ f : α → ℕ → Bool, Measurable f ∧ Function.Injective f := by
  rcases exists_seq_separating α MeasurableSet.empty univ with ⟨e, hem, he⟩
  refine ⟨(· ∈ e ·), ?_, ?_⟩
  · rw [measurable_pi_iff]
    refine fun n ↦ measurable_to_bool ?_
    simpa only [preimage, mem_singleton_iff, Bool.decide_iff, setOf_mem_eq] using hem n
  · exact fun x y h ↦ he x trivial y trivial fun n ↦ decide_eq_decide.1 <| congr_fun h _
#align measurable_space.measurable_injection_nat_bool_of_countably_generated MeasurableSpace.measurable_injection_nat_bool_of_countablyGenerated

end MeasurableSpace
