/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : Set α` is called *null measurable* (`MeasureTheory.NullMeasurableSet`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `MeasureTheory.toMeasurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `MeasurableSpace` instance on
`MeasureTheory.NullMeasurableSpace α μ`. We also say that `f : α → β` is
`MeasureTheory.NullMeasurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`MeasureTheory.NullMeasurableSpace α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `MeasurableSpace α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `MeasureTheory.Measure.completion μ` to be the same measure
interpreted as a measure on `MeasureTheory.NullMeasurableSpace α μ` and prove that this is a
complete measure.

## Implementation notes

We define `MeasureTheory.NullMeasurableSet` as `@MeasurableSet (NullMeasurableSpace α μ) _` so
that theorems about `MeasurableSet`s like `MeasurableSet.union` can be applied to
`NullMeasurableSet`s. However, these lemmas output terms of the same form
`@MeasurableSet (NullMeasurableSpace α μ) _ _`. While this is definitionally equal to the
expected output `NullMeasurableSet s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `MeasureTheory.NullMeasurableSet` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/

open Filter Set Encodable
open scoped ENNReal

variable {ι α β γ : Type*}

namespace MeasureTheory

/-- A type tag for `α` with `MeasurableSet` given by `NullMeasurableSet`. -/
@[nolint unusedArguments]
def NullMeasurableSpace (α : Type*) [MeasurableSpace α]
    (_μ : Measure α := by volume_tac) : Type _ :=
  α

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

instance NullMeasurableSpace.instInhabited [h : Inhabited α] :
    Inhabited (NullMeasurableSpace α μ) :=
  h

instance NullMeasurableSpace.instSubsingleton [h : Subsingleton α] :
    Subsingleton (NullMeasurableSpace α μ) :=
  h

instance NullMeasurableSpace.instMeasurableSpace : MeasurableSpace (NullMeasurableSpace α μ) :=
  @EventuallyMeasurableSpace α inferInstance (ae μ) _

/-- A set is called `NullMeasurableSet` if it can be approximated by a measurable set up to
a set of null measure. -/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by volume_tac) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp, aesop unsafe (rule_sets := [Measurable])]
theorem _root_.MeasurableSet.nullMeasurableSet (h : MeasurableSet s) : NullMeasurableSet s μ :=
  h.eventuallyMeasurableSet

theorem nullMeasurableSet_empty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty

theorem nullMeasurableSet_univ : NullMeasurableSet univ μ :=
  MeasurableSet.univ

namespace NullMeasurableSet

theorem of_null (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet sᶜ μ :=
  MeasurableSet.compl h

theorem of_compl (h : NullMeasurableSet sᶜ μ) : NullMeasurableSet s μ :=
  MeasurableSet.of_compl h

@[simp]
theorem compl_iff : NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff

@[nontriviality]
theorem of_subsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurableSet

protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ :=
  EventuallyMeasurableSet.congr hs h.symm

@[measurability]
protected theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) : NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.iUnion h

protected theorem biUnion {f : ι → Set α} {s : Set ι} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  MeasurableSet.biUnion hs h

protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀ s) μ := by
  rw [sUnion_eq_biUnion]
  exact MeasurableSet.biUnion hs h

@[measurability]
protected theorem iInter {ι : Sort*} [Countable ι] {f : ι → Set α}
    (h : ∀ i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.iInter h

protected theorem biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  MeasurableSet.biInter hs h

protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.sInter hs h

@[simp]
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∪ t) μ :=
  MeasurableSet.union hs ht

protected theorem union_null (hs : NullMeasurableSet s μ) (ht : μ t = 0) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union (of_null ht)

@[simp]
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∩ t) μ :=
  MeasurableSet.inter hs ht

@[simp]
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s \ t) μ :=
  MeasurableSet.diff hs ht

@[simp]
protected theorem symmDiff {s₁ s₂ : Set α} (h₁ : NullMeasurableSet s₁ μ)
    (h₂ : NullMeasurableSet s₂ μ) : NullMeasurableSet (symmDiff s₁ s₂) μ :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n

protected theorem const (p : Prop) : NullMeasurableSet { _a : α | p } μ :=
  MeasurableSet.const p

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  EventuallyMeasurableSpace.measurableSingleton (m := m0)

protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)]
    (hs : NullMeasurableSet s μ) (a : α) : NullMeasurableSet (insert a s) μ :=
  MeasurableSet.insert hs a

theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ t ⊇ s, MeasurableSet t ∧ t =ᵐ[μ] s := by
  rcases h with ⟨t, htm, hst⟩
  refine ⟨t ∪ toMeasurable μ (s \ t), ?_, htm.union (measurableSet_toMeasurable _ _), ?_⟩
  · exact diff_subset_iff.1 (subset_toMeasurable _ _)
  · have : toMeasurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using hst.symm.union this

theorem toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s := by
  rw [toMeasurable_def, dif_pos]
  exact (exists_measurable_superset_ae_eq h).choose_spec.2.2

theorem compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] s :=
  Iff.mpr ae_eq_set_compl <| toMeasurable_ae_eq h.compl

theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ t ⊆ s, MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨(toMeasurable μ sᶜ)ᶜ, compl_subset_comm.2 <| subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, compl_toMeasurable_compl_ae_eq h⟩

end NullMeasurableSet

open NullMeasurableSet

open scoped Function -- required for scoped `on` notation

/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
theorem exists_subordinate_pairwise_disjoint [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, t i ⊆ s i) ∧
        (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) := by
  choose t ht_sub htm ht_eq using fun i => exists_measurable_subset_ae_eq (h i)
  rcases exists_null_pairwise_disjoint_diff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => diff_subset.trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (diff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diff (hum i),
      hud.mono fun i j h =>
        h.mono (diff_subset_diff_left (ht_sub i)) (diff_subset_diff_left (ht_sub j))⟩

theorem measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι → Set α}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rw [measure_eq_extend (MeasurableSet.iUnion h),
    extend_iUnion MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_iUnion

theorem measure_iUnion₀ [Countable ι] {f : ι → Set α} (hd : Pairwise (AEDisjoint μ on f))
    (h : ∀ i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (EventuallyEq.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := measure_iUnion htd htm
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm

theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hd : AEDisjoint μ s t) : μ (s ∪ t) = μ s + μ t := by
  rw [union_eq_iUnion, measure_iUnion₀, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts [(pairwise_on_bool AEDisjoint.symmetric).2 hd, fun b => Bool.casesOn b ht hs]

/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem measure_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∩ t) + μ (s \ t) = μ s := by
  refine le_antisymm ?_ (measure_le_inter_add_diff _ _ _)
  rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
  replace hs'm : NullMeasurableSet s' μ := hs'm.nullMeasurableSet
  calc
    μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) := by gcongr
    _ = μ (s' ∩ t ∪ s' \ t) :=
      (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
          (@disjoint_inf_sdiff _ s' t _).aedisjoint).symm
    _ = μ s' := congr_arg μ (inter_union_diff _ _)
    _ = μ s := hs'

/-- If `s` and `t` are null measurable sets of equal measure
and their intersection has finite measure,
then `s \ t` and `t \ s` have equal measures too. -/
theorem measure_diff_symm (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (h : μ s = μ t) (hfin : μ (s ∩ t) ≠ ∞) : μ (s \ t) = μ (t \ s) := by
  rw [← ENNReal.add_right_inj hfin, measure_inter_add_diff₀ _ ht, inter_comm,
    measure_inter_add_diff₀ _ hs, h]

theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]

theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_comm]

theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [← measure_union_add_inter₀ s ht, hd, add_zero]

theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [union_comm, measure_union₀ hs (AEDisjoint.symm hd), add_comm]

theorem measure_add_measure_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    μ s + μ sᶜ = μ univ := by rw [← measure_union₀' hs aedisjoint_compl_right, union_compl_self]

lemma measure_of_measure_compl_eq_zero (hs : μ sᶜ = 0) : μ s = μ Set.univ := by
  simpa [hs] using measure_add_measure_compl₀ <| .of_compl <| .of_null hs

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

theorem nullMeasurableSet_singleton (x : α) : NullMeasurableSet {x} μ :=
  @measurableSet_singleton _ _ _ _

@[simp]
theorem nullMeasurableSet_insert {a : α} {s : Set α} :
    NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurableSet_insert

theorem nullMeasurableSet_eq {a : α} : NullMeasurableSet { x | x = a } μ :=
  nullMeasurableSet_singleton a

protected theorem _root_.Set.Finite.nullMeasurableSet (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurableSet hs

protected theorem _root_.Finset.nullMeasurableSet (s : Finset α) : NullMeasurableSet (↑s) μ := by
  apply Finset.measurableSet

end MeasurableSingletonClass

theorem _root_.Set.Finite.nullMeasurableSet_biUnion {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finite.measurableSet_biUnion hs h

theorem _root_.Finset.nullMeasurableSet_biUnion {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finset.measurableSet_biUnion s h

theorem _root_.Set.Finite.nullMeasurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀ s) μ :=
  Finite.measurableSet_sUnion hs h

theorem _root_.Set.Finite.nullMeasurableSet_biInter {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  Finite.measurableSet_biInter hs h

theorem _root_.Finset.nullMeasurableSet_biInter {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  s.finite_toSet.nullMeasurableSet_biInter h

theorem _root_.Set.Finite.nullMeasurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter (Finite.countable hs) h

theorem nullMeasurableSet_toMeasurable : NullMeasurableSet (toMeasurable μ s) μ :=
  (measurableSet_toMeasurable _ _).nullMeasurableSet

variable [MeasurableSingletonClass α] {mβ : MeasurableSpace β} [MeasurableSingletonClass β]

lemma measure_preimage_fst_singleton_eq_tsum [Countable β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑' y, μ {(x, y)} := by
  rw [← measure_iUnion (by simp [Pairwise]) fun _ ↦ .singleton _, iUnion_singleton_eq_range,
    preimage_fst_singleton_eq_range]

lemma measure_preimage_snd_singleton_eq_tsum [Countable α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑' x, μ {(x, y)} := by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this, measure_iUnion] <;> simp [Pairwise]

lemma measure_preimage_fst_singleton_eq_sum [Fintype β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑ y, μ {(x, y)} := by
  rw [measure_preimage_fst_singleton_eq_tsum μ x, tsum_fintype]

lemma measure_preimage_snd_singleton_eq_sum [Fintype α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑ x, μ {(x, y)} := by
  rw [measure_preimage_snd_singleton_eq_tsum μ y, tsum_fintype]

end

section NullMeasurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measure α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def NullMeasurable (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ

protected theorem _root_.Measurable.nullMeasurable (h : Measurable f) : NullMeasurable f μ :=
  h.eventuallyMeasurable

protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) :
    @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h

theorem Measurable.comp_nullMeasurable {g : β → γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ :=
  hg.comp_eventuallyMeasurable hf

theorem NullMeasurable.congr {g : α → β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) :
    NullMeasurable g μ :=
  EventuallyMeasurable.congr hf hg.symm

end NullMeasurable

section IsComplete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : ∀ s, μ s = 0 → MeasurableSet s

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

theorem Measure.isComplete_iff : μ.IsComplete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem Measure.IsComplete.out (h : μ.IsComplete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1

theorem measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs

theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] :
    MeasurableSet s :=
  diff_diff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diff
      (measurableSet_of_null (ae_le_set.1 <|
        EventuallyEq.le (NullMeasurableSet.toMeasurable_ae_eq hs)))

theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {_m1 : MeasurableSpace β} {f : α → β}
    (hf : NullMeasurable f μ) : Measurable f := fun _s hs => (hf hs).measurable_of_complete

theorem _root_.Measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [_hμ : μ.IsComplete] {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  NullMeasurable.measurable_of_complete (NullMeasurable.congr hf.nullMeasurable hfg)

namespace Measure

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : MeasurableSpace α} (μ : Measure α) :
    MeasureTheory.Measure (NullMeasurableSpace α μ) where
  toOuterMeasure := μ.toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint) hs
  trim_le := by
    nth_rewrite 2 [← μ.trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ fun _ ↦ MeasurableSet.nullMeasurableSet

instance completion.isComplete {_m : MeasurableSpace α} (μ : Measure α) : μ.completion.IsComplete :=
  ⟨fun _z hz => NullMeasurableSet.of_null hz⟩

@[simp]
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.completion = μ :=
  rfl

theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.completion s = μ s :=
  rfl

@[simp]
theorem ae_completion {_ : MeasurableSpace α} (μ : Measure α) : ae μ.completion = ae μ := rfl

end Measure

end IsComplete

end MeasureTheory
