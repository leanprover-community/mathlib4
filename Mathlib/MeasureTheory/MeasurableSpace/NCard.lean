import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Card

open Set

instance ENat.instCountable : Countable ℕ∞ := instCountableOption
instance ENat.instMeasurableSpace : MeasurableSpace ℕ∞ := ⊤
instance ENat.instDiscreteMeasurableSpace : DiscreteMeasurableSpace ℕ∞ := ⟨fun _ ↦ trivial⟩
instance ENat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ∞ := inferInstance

theorem ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α → ℕ∞} :
    Measurable f ↔ ∀ n : ℕ, MeasurableSet (f ⁻¹' {↑n}) := by
  refine ⟨fun hf n ↦ hf <| measurableSet_singleton _, fun h ↦ measurable_to_countable' fun n ↦ ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top, ← compl_range_some, preimage_compl, ← iUnion_singleton_eq_range,
      preimage_iUnion]
    exact .compl <| .iUnion h
  | coe n => exact h n

theorem Set.encard_eq_coe_iff_finset {α : Type*} {s : Set α} {n : ℕ} :
    s.encard = n ↔ ∃ t : Finset α, t.card = n ∧ ↑t = s := by
  if hs : s.Finite then
    lift s to Finset α using hs
    simp
  else
    have : ∀ t : Finset α, ↑t ≠ s := by rintro t rfl; simp at hs
    simp [Set.Infinite.encard_eq hs, this]

@[simp]
theorem Set.range_finsetToSet {α : Type*} : range ((↑) : Finset α → Set α) = {s | s.Finite} :=
  (range_subset_iff.2 fun s ↦ s.finite_toSet).antisymm <| fun _s hs ↦ ⟨hs.toFinset, hs.coe_toFinset⟩

variable {α : Type*} [Countable α]

theorem Set.countable_setOf_finite : Set.Countable {s : Set α | s.Finite} := by
  simpa using countable_setOf_finite_subset countable_univ

@[measurability]
theorem measurable_encard : Measurable (Set.encard : Set α → ℕ∞) :=
  ENat.measurable_iff.2 fun _n ↦ Countable.measurableSet <| countable_setOf_finite.mono fun _s hs ↦
    finite_of_encard_eq_coe hs

@[measurability]
theorem measurable_ncard : Measurable (Set.ncard : Set α → ℕ) :=
  (measurable_discrete ENat.toNat).comp measurable_encard

@[measurability]
theorem measurableSet_setOf_finite : MeasurableSet {s : Set α | s.Finite} :=
  countable_setOf_finite.measurableSet

@[measurability]
theorem measurableSet_setOf_infinite : MeasurableSet {s : Set α | s.Infinite} :=
  measurableSet_setOf_finite.compl
