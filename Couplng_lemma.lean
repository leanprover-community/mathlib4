import Mathlib

open scoped BigOperators symmDiff
open MeasureTheory

noncomputable section

lemma tsum_restrict_preimage_singleton_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : Set Ω} {f : Ω → ℕ} (hf : Measurable f) :
    (∑' k : ℕ, μ.restrict s (f ⁻¹' ({k} : Set ℕ))) = μ s := by
  calc
  _ = ∑' b : (Set.univ : Set ℕ), μ.restrict s (f ⁻¹' ({(b : ℕ)} : Set ℕ)) := by
    simpa using (tsum_subtype (Set.univ : Set ℕ)
      (fun k : ℕ => μ.restrict s (f ⁻¹' ({k} : Set ℕ)))).symm
  _ = _ := by
    simpa using tsum_measure_preimage_singleton (μ := μ.restrict s) (s := (⊤ : Set ℕ))
      (Set.to_countable _) (fun k _ => hf (measurableSet_singleton k))

lemma tsum_measureReal_restrict_preimage_singleton_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → ℕ} (hf : Measurable f) :
    (∑' k : ℕ, (μ.restrict s).real (f ⁻¹' ({k} : Set ℕ))) = μ.real s := by
  simp_rw [Measure.real]
  rw [← ENNReal.tsum_toReal_eq]
  · rw [tsum_restrict_preimage_singleton_eq (μ := μ) (s := s) hf]
  · intro k
    finiteness

lemma coupling_term_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y Z : Ω → ℕ} (hY : Measurable Y) (hZ : Measurable Z) (k : ℕ) :
    |(μ.map Y).real {k} - (μ.map Z).real {k}| ≤
      (μ.restrict {ω | Y ω ≠ Z ω}).real (Y ⁻¹' ({k} : Set ℕ)) +
      (μ.restrict {ω | Y ω ≠ Z ω}).real (Z ⁻¹' ({k} : Set ℕ)) := by
  let E : Set Ω := {ω | Y ω ≠ Z ω}
  let A : Set Ω := Y ⁻¹' ({k} : Set ℕ)
  let B : Set Ω := Z ⁻¹' ({k} : Set ℕ)
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

theorem coupling_lemma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y Z : Ω → ℕ} (hY : Measurable Y) (hZ : Measurable Z) :
    (∑' k : ℕ, |(μ.map Y).real {k} - (μ.map Z).real {k}|) ≤ 2 * μ.real {ω | Y ω ≠ Z ω} := by
  let E : Set Ω := {ω | Y ω ≠ Z ω}
  have hsY : Summable (fun k : ℕ => (μ.restrict E).real (Y ⁻¹' ({k} : Set ℕ))) :=
    summable_measure_toReal (fun k => hY (measurableSet_singleton k)) (pairwise_disjoint_fiber Y)
  have hsZ : Summable (fun k : ℕ => (μ.restrict E).real (Z ⁻¹' ({k} : Set ℕ))) :=
    summable_measure_toReal (fun k => hZ (measurableSet_singleton k)) (pairwise_disjoint_fiber Z)
  calc
    _ ≤ ∑' k : ℕ, ((μ.restrict E).real (Y ⁻¹' ({k} : Set ℕ)) +
        (μ.restrict E).real (Z ⁻¹' ({k} : Set ℕ))) := by
      refine Summable.tsum_le_tsum (coupling_term_bound (μ := μ) hY hZ) ?_ (hsY.add hsZ)
      exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) (coupling_term_bound (μ := μ) hY hZ)
        (hsY.add hsZ)
    _ = (∑' k : ℕ, (μ.restrict E).real (Y ⁻¹' ({k} : Set ℕ))) +
        (∑' k : ℕ, (μ.restrict E).real (Z ⁻¹' ({k} : Set ℕ))) := hsY.tsum_add hsZ
    _ = μ.real E + μ.real E := by
      rw [tsum_measureReal_restrict_preimage_singleton_eq (μ := μ) (s := E) hY,
        tsum_measureReal_restrict_preimage_singleton_eq (μ := μ) (s := E) hZ]
    _ = 2 * μ.real E := by ring
