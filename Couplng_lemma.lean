import Mathlib

open scoped BigOperators symmDiff
open MeasureTheory

noncomputable section

lemma tsum_restrict_preimage_singleton_eq' {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] {μ : Measure Ω} {s : Set Ω} {f : Ω → S}
    (hf : Measurable f) :
    (∑' k : S, μ.restrict s (f ⁻¹' ({k} : Set S))) = μ s := by
  sorry

lemma tsum_measureReal_restrict_preimage_singleton_eq {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] {μ : Measure Ω}
    [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → S} (hf : Measurable f) :
    (∑' k : S, (μ.restrict s).real (f ⁻¹' ({k} : Set S))) = μ.real s := by
  simp_rw [Measure.real]
  rw [← ENNReal.tsum_toReal_eq]
  · rw [tsum_restrict_preimage_singleton_eq (μ := μ) (s := s) hf]
  · intro k
    finiteness

lemma coupling_term_bound {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] {μ : Measure Ω} [IsFiniteMeasure μ] {Y Z : Ω → S}
    (hY : Measurable Y) (hZ : Measurable Z) (k : S) :
    |(μ.map Y).real ({k} : Set S) - (μ.map Z).real ({k} : Set S)| ≤
      (μ.restrict {ω | Y ω ≠ Z ω}).real (Y ⁻¹' ({k} : Set S)) +
      (μ.restrict {ω | Y ω ≠ Z ω}).real (Z ⁻¹' ({k} : Set S)) := by
  let E : Set Ω := {ω | Y ω ≠ Z ω}
  let A : Set Ω := Y ⁻¹' ({k} : Set S)
  let B : Set Ω := Z ⁻¹' ({k} : Set S)
  have hE : MeasurableSet E := by
    convert (measurableSet_eq_fun hY hZ).compl using 1
  have hA : MeasurableSet A := by
    simpa [A] using hY (measurableSet_singleton k)
  have hB : MeasurableSet B := by
    simpa [B] using hZ (measurableSet_singleton k)
  have hsubset : A ∆ B ⊆ E := by
    simpa [A, B, E] using by grind
  rw [map_measureReal_apply hY (measurableSet_singleton k),
    map_measureReal_apply hZ (measurableSet_singleton k)]
  calc
    _ ≤ μ.real (A ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hB.nullMeasurableSet
    _ = μ.real (A ∆ B ∩ E) := by rw [Set.inter_eq_left.mpr hsubset]
    _ = (μ.restrict E).real (A \ B) + (μ.restrict E).real (B \ A) := by
      rw [← measureReal_restrict_apply' hE, measureReal_symmDiff_eq (μ := μ.restrict E) hA hB]
    _ ≤ (μ.restrict E).real A + (μ.restrict E).real B :=
      add_le_add (measureReal_mono Set.diff_subset) (measureReal_mono Set.diff_subset)

theorem coupling_lemma {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] {μ : Measure Ω} [IsProbabilityMeasure μ] {Y Z : Ω → S}
    (hY : Measurable Y) (hZ : Measurable Z) :
    (∑' k : S, |(μ.map Y).real ({k} : Set S) - (μ.map Z).real ({k} : Set S)|) ≤
      2 * μ.real {ω | Y ω ≠ Z ω} := by
  let E : Set Ω := {ω | Y ω ≠ Z ω}
  have hsY : Summable (fun k : S => (μ.restrict E).real (Y ⁻¹' ({k} : Set S))) := by
    refine ENNReal.summable_toReal ?_
    rw [tsum_restrict_preimage_singleton_eq (μ := μ) (s := E) hY]
    finiteness
  have hsZ : Summable (fun k : S => (μ.restrict E).real (Z ⁻¹' ({k} : Set S))) := by
    refine ENNReal.summable_toReal ?_
    rw [tsum_restrict_preimage_singleton_eq (μ := μ) (s := E) hZ]
    finiteness
  calc
    _ ≤ ∑' k : S, ((μ.restrict E).real (Y ⁻¹' ({k} : Set S)) +
        (μ.restrict E).real (Z ⁻¹' ({k} : Set S))) := by
      refine Summable.tsum_le_tsum (coupling_term_bound (μ := μ) hY hZ) ?_ (hsY.add hsZ)
      exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) (coupling_term_bound (μ := μ) hY hZ)
        (hsY.add hsZ)
    _ = (∑' k : S, (μ.restrict E).real (Y ⁻¹' ({k} : Set S))) +
        (∑' k : S, (μ.restrict E).real (Z ⁻¹' ({k} : Set S))) := hsY.tsum_add hsZ
    _ = μ.real E + μ.real E := by
      rw [tsum_measureReal_restrict_preimage_singleton_eq (μ := μ) (s := E) hY,
        tsum_measureReal_restrict_preimage_singleton_eq (μ := μ) (s := E) hZ]
    _ = 2 * μ.real E := by ring
