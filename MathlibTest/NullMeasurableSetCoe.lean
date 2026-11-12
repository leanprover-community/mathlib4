module
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Tests for the coercion from `MeasurableSet s` to `NullMeasurableSet s μ`. -/

open MeasureTheory Function

variable {α : Type*} [m0 : MeasurableSpace α] {μ : Measure α} {s t : Set α}

-- As the argument of a lemma.
example (ht : MeasurableSet t) (hd : AEDisjoint μ s t) : μ (s ∪ t) = μ s + μ t :=
  measure_union₀ ht hd

-- The measure is only determined by a later argument.
example (ht : MeasurableSet t) (hd : AEDisjoint μ s t) : True := by
  have := measure_union₀ ht hd
  trivial

-- A set that is measurable for a sub-σ-algebra.
example {m : MeasurableSpace α} (hm : m ≤ m0) (hs : MeasurableSet[m] s)
    (hd : AEDisjoint μ t s) : μ (t ∪ s) = μ t + μ s :=
  measure_union₀ (hm s hs) hd

-- Families of sets, after eta-expanding.
example {ι : Type*} [Countable ι] {f : ι → Set α} (hd : Pairwise (AEDisjoint μ on f))
    (hf : ∀ i, MeasurableSet (f i)) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  measure_iUnion₀ hd fun i ↦ hf i

-- Expected types and anonymous constructors.
example (hs : MeasurableSet s) : NullMeasurableSet s μ := hs

example (hs : MeasurableSet s) (ht : MeasurableSet t) :
    NullMeasurableSet s μ ∧ NullMeasurableSet t μ :=
  ⟨hs, ht⟩
