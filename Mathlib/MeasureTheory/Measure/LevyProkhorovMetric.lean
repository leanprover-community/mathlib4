/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The Lévy-Prokhorov distance on spaces of finite measures and probability measures

## Main definitions

* `MeasureTheory.levyProkhorovEDist`: The Lévy-Prokhorov edistance between two measures.
* `MeasureTheory.levyProkhorovDist`: The Lévy-Prokhorov distance between two finite measures.

## Main results

* `levyProkhorovDist_pseudoMetricSpace_finiteMeasure`: The Lévy-Prokhorov distance is a
  pseudoemetric on the space of finite measures.
* `levyProkhorovDist_pseudoMetricSpace_probabilityMeasure`: The Lévy-Prokhorov distance is a
  pseudoemetric on the space of probability measures.

## Todo

* Show that in Borel spaces, the Lévy-Prokhorov distance is a metric; not just a pseudometric.
* Prove that if `X` is metrizable and separable, then the Lévy-Prokhorov distance metrizes the
  topology of weak convergence.

## Tags

finite measure, probability measure, weak convergence, convergence in distribution, metrizability
-/

open Topology Metric Filter Set ENNReal NNReal

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Levy_Prokhorov

/-! ### Lévy-Prokhorov metric -/

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω]

/-- The Lévy-Prokhorov edistance between measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
noncomputable def levyProkhorovEDist (μ ν : Measure Ω) : ℝ≥0∞ :=
  sInf {ε | ∀ B, MeasurableSet B →
            μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε}

lemma meas_le_of_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : ℝ≥0∞} (μ ν : Measure Ω)
    (h_le : ε₁ ≤ ε₂) {B : Set Ω} (hε₁ : μ B ≤ ν (thickening ε₁.toReal B) + ε₁):
    μ B ≤ ν (thickening ε₂.toReal B) + ε₂ := by
  by_cases ε_top : ε₂ = ∞
  · simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ε_top, top_toReal,
                add_top, le_top]
  apply hε₁.trans (add_le_add ?_ h_le)
  exact measure_mono (μ := ν) (thickening_mono (toReal_mono ε_top h_le) B)

lemma left_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) :
    μ B ≤ ν (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact measure_apply_le_of_le_of_forall_le_measure_thickening_add μ ν lt_c.le (hc' B B_mble).1

lemma right_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) :
    ν B ≤ μ (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact measure_apply_le_of_le_of_forall_le_measure_thickening_add ν μ lt_c.le (hc' B B_mble).2

lemma levyProkhorovEDist_le_of_forall_add_pos_le (μ ν : Measure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, 0 < ε → ε < ∞ → MeasurableSet B →
      μ B ≤ ν (thickening (δ + ε).toReal B) + δ + ε ∧
      ν B ≤ μ (thickening (δ + ε).toReal B) + δ + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  by_cases ε_top : ε = ∞
  · simp only [ε_top, add_top, le_top]
  apply sInf_le
  intro B B_mble
  simpa only [add_assoc] using h ε B (coe_pos.mpr hε) coe_lt_top B_mble

lemma levyProkhorovEDist_le_of_forall (μ ν : Measure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B →
        μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  by_cases δ_top : δ = ∞
  · simp only [δ_top, add_top, le_top]
  apply levyProkhorovEDist_le_of_forall_add_pos_le
  intro x B x_pos x_lt_top B_mble
  simpa only [← add_assoc] using h (δ + x) B (ENNReal.lt_add_right δ_top x_pos.ne.symm)
    (by simp only [add_lt_top, Ne.lt_top δ_top, x_lt_top, and_self]) B_mble

lemma levyProkhorovEDist_le_max_measure_univ (μ ν : Measure Ω) :
    levyProkhorovEDist μ ν ≤ max (μ univ) (ν univ) := by
  refine sInf_le fun B _ ↦ ⟨?_, ?_⟩ <;> apply le_add_left <;> simp [measure_mono]

lemma levyProkhorovEDist_lt_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν < ∞ :=
  (levyProkhorovEDist_le_max_measure_univ μ ν).trans_lt <| by simp [measure_lt_top]

lemma levyProkhorovEDist_self (μ : Measure Ω) :
    levyProkhorovEDist μ μ = 0 := by
  rw [← nonpos_iff_eq_zero, ← csInf_Ioo zero_lt_top]
  refine sInf_le_sInf fun ε ⟨hε₀, hε_top⟩ B _ ↦ and_self_iff.2 ?_
  refine le_add_right <| measure_mono <| self_subset_thickening ?_ _
  exact ENNReal.toReal_pos hε₀.ne' hε_top.ne

lemma levyProkhorovEDist_comm (μ ν : Measure Ω) :
    levyProkhorovEDist μ ν = levyProkhorovEDist ν μ := by
  simp only [levyProkhorovEDist, and_comm]

lemma levyProkhorovEDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω) :
    levyProkhorovEDist μ κ ≤ levyProkhorovEDist μ ν + levyProkhorovEDist ν κ := by
  by_cases LPμν_finite : levyProkhorovEDist μ ν = ∞
  · simp [LPμν_finite]
  by_cases LPνκ_finite : levyProkhorovEDist ν κ = ∞
  · simp [LPνκ_finite]
  apply levyProkhorovEDist_le_of_forall_add_pos_le
  intro ε B ε_pos ε_lt_top B_mble
  have half_ε_pos : 0 < ε / 2 := ENNReal.div_pos ε_pos.ne' two_ne_top
  have half_ε_lt_top : ε / 2 < ∞ := ENNReal.div_lt_top ε_lt_top.ne two_ne_zero
  let r := levyProkhorovEDist μ ν + ε / 2
  let s := levyProkhorovEDist ν κ + ε / 2
  have lt_r : levyProkhorovEDist μ ν < r := lt_add_right LPμν_finite half_ε_pos.ne'
  have lt_s : levyProkhorovEDist ν κ < s := lt_add_right LPνκ_finite half_ε_pos.ne'
  have hs_add_r : s + r = levyProkhorovEDist μ ν + levyProkhorovEDist ν κ + ε := by
    simp_rw [add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves, ← add_assoc,
      add_comm (levyProkhorovEDist μ ν)]
  have hs_add_r' : s.toReal + r.toReal
      = (levyProkhorovEDist μ ν + levyProkhorovEDist ν κ + ε).toReal := by
    rw [← hs_add_r, ← ENNReal.toReal_add]
    · exact ENNReal.add_ne_top.mpr ⟨LPνκ_finite, half_ε_lt_top.ne⟩
    · exact ENNReal.add_ne_top.mpr ⟨LPμν_finite, half_ε_lt_top.ne⟩
  rw [← hs_add_r', add_assoc, ← hs_add_r, add_assoc _ _ ε, ← hs_add_r]
  refine ⟨?_, ?_⟩
  · calc μ B ≤ ν (thickening r.toReal B) + r :=
      left_measure_le_of_levyProkhorovEDist_lt lt_r B_mble
    _ ≤ κ (thickening s.toReal (thickening r.toReal B)) + s + r :=
      add_le_add_right
        (left_measure_le_of_levyProkhorovEDist_lt lt_s isOpen_thickening.measurableSet) _
    _ = κ (thickening s.toReal (thickening r.toReal B)) + (s + r) := add_assoc _ _ _
    _ ≤ κ (thickening (s.toReal + r.toReal) B) + (s + r) :=
      add_le_add_right (measure_mono (thickening_thickening_subset _ _ _)) _
  · calc κ B ≤ ν (thickening s.toReal B) + s :=
      right_measure_le_of_levyProkhorovEDist_lt lt_s B_mble
    _ ≤ μ (thickening r.toReal (thickening s.toReal B)) + r + s :=
      add_le_add_right
        (right_measure_le_of_levyProkhorovEDist_lt lt_r isOpen_thickening.measurableSet) s
    _ = μ (thickening r.toReal (thickening s.toReal B)) + (s + r) := by rw [add_assoc, add_comm r]
    _ ≤ μ (thickening (r.toReal + s.toReal) B) + (s + r) :=
      add_le_add_right (measure_mono (thickening_thickening_subset _ _ _)) _
    _ = μ (thickening (s.toReal + r.toReal) B) + (s + r) := by rw [add_comm r.toReal]

/-- The Lévy-Prokhorov distance between finite measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
noncomputable def levyProkhorovDist (μ ν : Measure Ω) : ℝ :=
  (levyProkhorovEDist μ ν).toReal

lemma levyProkhorovDist_self (μ : Measure Ω) :
    levyProkhorovDist μ μ = 0 := by
  simp only [levyProkhorovDist, levyProkhorovEDist_self, zero_toReal]

lemma levyProkhorovDist_comm (μ ν : Measure Ω) :
    levyProkhorovDist μ ν = levyProkhorovDist ν μ := by
  simp only [levyProkhorovDist, levyProkhorovEDist_comm]

lemma levyProkhorovDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    levyProkhorovDist μ κ ≤ levyProkhorovDist μ ν + levyProkhorovDist ν κ := by
  have dμκ_finite := (levyProkhorovEDist_lt_top μ κ).ne
  have dμν_finite := (levyProkhorovEDist_lt_top μ ν).ne
  have dνκ_finite := (levyProkhorovEDist_lt_top ν κ).ne
  convert (ENNReal.toReal_le_toReal (a := levyProkhorovEDist μ κ)
    (b := levyProkhorovEDist μ ν + levyProkhorovEDist ν κ)
    _ _).mpr <| levyProkhorovEDist_triangle μ ν κ
  · simp only [levyProkhorovDist, ENNReal.toReal_add dμν_finite dνκ_finite]
  · exact dμκ_finite
  · exact ENNReal.add_ne_top.mpr ⟨dμν_finite, dνκ_finite⟩

/-- A type synonym, to be used for `Measure α`, `FiniteMeasure α`, or `ProbabilityMeasure α`,
when they are to be equipped with the Lévy-Prokhorov distance. -/
def LevyProkhorov (α : Type*) := α

variable [OpensMeasurableSpace Ω]

/-- The Lévy-Prokhorov distance `levyProkhorovEDist` makes `Measure Ω` a pseudoemetric
space. The instance is recorded on the type synonym `LevyProkhorov (Measure Ω) := Measure Ω`. -/
noncomputable instance : PseudoEMetricSpace (LevyProkhorov (Measure Ω)) where
  edist := levyProkhorovEDist
  edist_self := levyProkhorovEDist_self
  edist_comm := levyProkhorovEDist_comm
  edist_triangle := levyProkhorovEDist_triangle

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `FiniteMeasure Ω` a pseudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (FiniteMeasure Ω) := FiniteMeasure Ω`. -/
noncomputable instance levyProkhorovDist_pseudoMetricSpace_finiteMeasure :
    PseudoMetricSpace (LevyProkhorov (FiniteMeasure Ω)) where
  dist μ ν := levyProkhorovDist μ.toMeasure ν.toMeasure
  dist_self μ := levyProkhorovDist_self _
  dist_comm μ ν := levyProkhorovDist_comm _ _
  dist_triangle μ ν κ := levyProkhorovDist_triangle _ _ _
  edist_dist μ ν := by simp [← ENNReal.ofReal_coe_nnreal]

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `ProbabilityMeasure Ω` a pseudoemetric
space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`. -/
noncomputable instance levyProkhorovDist_pseudoMetricSpace_probabilityMeasure :
    PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) where
  dist μ ν := levyProkhorovDist μ.toMeasure ν.toMeasure
  dist_self μ := levyProkhorovDist_self _
  dist_comm μ ν := levyProkhorovDist_comm _ _
  dist_triangle μ ν κ := levyProkhorovDist_triangle _ _ _
  edist_dist μ ν := by simp [← ENNReal.ofReal_coe_nnreal]

end Levy_Prokhorov --section

end MeasureTheory -- namespace
