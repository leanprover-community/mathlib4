import Mathlib.MeasureTheory.Constructions.Projective

open MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}
  {I J : Finset ι}

lemma measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J ⊆ I) :
    P I Set.univ = P J Set.univ := by
  classical
  have : (Set.univ : Set (∀ i : I, α i)) =
      Set.restrict₂ hJI ⁻¹' (Set.univ : Set (∀ i : J, α i)) := by
    rw [Set.preimage_univ]
  rw [this, ← Measure.map_apply _ MeasurableSet.univ] -- What happens here?
  · rw [hP I J hJI]
    rfl -- why is this necessary?
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
