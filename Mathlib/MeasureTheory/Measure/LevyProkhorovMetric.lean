/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# The Lévy-Prokhorov distance on spaces of finite measures and probability measures

## Main definitions

* `FiniteMeasure.LPedist`: The Lévy-Prokhorov distance between two finite measures.

## Main results

* `LPedist_pseudoEMetricSpace`: The Lévy-Prokhorov distance is a pseudoemetric on the space of
  finite measures.

## Todo

* Show that in Borel spaces, the Lévy-Prokhorov distance is a metric; not just a pseudometric.
* Add Lévy-Prokhorov distance for probability measures.
* Prove that if `X` is metrizable and separable, then the Lévy-Prokhorov distance metrizes the
  topology of weak convergence.

## Tags

finite measure, probability measure, weak convergence, convergence in distribution, metrizability
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Levy_Prokhorov

/-! ### Lévy-Prokhorov metric -/

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]
variable [MetricSpace Ω] [OpensMeasurableSpace Ω]

/-- The Lévy-Prokhorov distance on the space of finite measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
noncomputable def LPedist (μ ν : FiniteMeasure Ω) : ℝ≥0∞ :=
  sInf {ε | ∀ B, MeasurableSet B →
            μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε}

lemma LPedist_monotone_set {ε₁ ε₂ : ℝ≥0∞} (μ ν : FiniteMeasure Ω) (h_le : ε₁ ≤ ε₂)
    (hε₁ : ∀ B, MeasurableSet B →
      μ B ≤ ν (thickening ε₁.toReal B) + ε₁ ∧ ν B ≤ μ (thickening ε₁.toReal B) + ε₁)
    {B : Set Ω} (B_mble : MeasurableSet B) :
    μ B ≤ ν (thickening ε₂.toReal B) + ε₂ ∧ ν B ≤ μ (thickening ε₂.toReal B) + ε₂ := by
  specialize hε₁ B B_mble
  simp only [ne_eq] at *
  refine ⟨?_, ?_⟩
  · by_cases ε_top : ε₂ = ∞
    · simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ε_top, top_toReal,
                 add_top, le_top]
    apply hε₁.1.trans (add_le_add ?_ h_le)
    simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at *
    exact measure_mono (μ := ν) (thickening_mono (toReal_mono ε_top h_le) B)
  · by_cases ε_top : ε₂ = ∞
    · simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ε_top, top_toReal,
                 add_top, le_top]
    apply hε₁.2.trans (add_le_add ?_ h_le)
    simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at *
    exact measure_mono (μ := μ) (thickening_mono (toReal_mono ε_top h_le) B)

lemma left_measure_le_of_LPedist_lt {μ ν : FiniteMeasure Ω} {c : ℝ≥0∞} (h : LPedist μ ν < c)
    {B : Set Ω} (B_mble : MeasurableSet B) :
    μ B ≤ ν (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact (LPedist_monotone_set μ ν lt_c.le hc' B_mble).1

lemma right_measure_le_of_LPedist_lt {μ ν : FiniteMeasure Ω} {c : ℝ≥0∞} (h : LPedist μ ν < c)
    {B : Set Ω} (B_mble : MeasurableSet B) :
    ν B ≤ μ (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact (LPedist_monotone_set μ ν lt_c.le hc' B_mble).2

lemma LPedist_le_of_forall (μ ν : FiniteMeasure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B →
      μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε) :
    LPedist μ ν ≤ δ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε δ_lt_top
  by_cases ε_top : ε = ∞
  · simp only [ε_top, add_top, le_top]
  apply sInf_le
  simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, mem_setOf_eq]
  intro B B_mble
  convert h (δ + ε) B ?_ ?_ B_mble
  · exact (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure _ _).symm
  · exact (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure _ _).symm
  · exact (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure _ _).symm
  · exact (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure _ _).symm
  · simpa only [add_zero] using ENNReal.add_lt_add_left (a := δ) δ_lt_top.ne (coe_pos.mpr hε)
  · simp only [add_lt_top, δ_lt_top, coe_lt_top, and_self]

lemma LPedist_le_of_forall_add_pos_le (μ ν : FiniteMeasure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, 0 < ε → ε < ∞ → MeasurableSet B →
      μ B ≤ ν (thickening (δ + ε).toReal B) + δ + ε ∧
      ν B ≤ μ (thickening (δ + ε).toReal B) + δ + ε) :
    LPedist μ ν ≤ δ := by
  apply LPedist_le_of_forall μ ν δ
  intro x B δ_lt_x x_lt_top B_mble
  have pos : 0 < x - δ := by exact tsub_pos_of_lt δ_lt_x
  simpa [add_assoc, add_tsub_cancel_of_le δ_lt_x.le]
    using h (x - δ) B pos (tsub_lt_of_lt x_lt_top) B_mble

lemma LPedist.le_max_mass (μ ν : FiniteMeasure Ω) :
    LPedist μ ν ≤ max μ.mass ν.mass := by
  apply sInf_le
  simp only [ENNReal.coe_max, FiniteMeasure.ennreal_mass, ge_iff_le, ne_eq,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, mem_setOf_eq]
  intro B _
  refine ⟨(measure_mono (subset_univ B)).trans ?_, (measure_mono (subset_univ B)).trans ?_⟩
  · apply le_add_left
    apply le_max_left
  · apply le_add_left
    apply le_max_right

lemma LPedist.lt_top (μ ν : FiniteMeasure Ω) :
    LPedist μ ν < ∞ :=
  lt_of_le_of_lt (LPedist.le_max_mass μ ν) coe_lt_top

lemma LPedist.self (μ : FiniteMeasure Ω) :
    LPedist μ μ = 0 := by
  by_cases zero_meas : μ = 0
  · simp [zero_meas, LPedist, FiniteMeasure.toMeasure_zero]
  simp_rw [← FiniteMeasure.mass_nonzero_iff] at zero_meas
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt (by simp)
  simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, and_self, mem_setOf_eq]
  intro ε ε_pos
  have half_ε_pos : 0 < ε/2 := by
    simp only [ENNReal.div_pos_iff, ne_eq, ε_pos.ne.symm, not_false_eq_true, two_ne_top, and_self]
  refine ⟨min (ε/2) μ.mass, ⟨?_, ?_⟩⟩
  · intro B _
    apply le_add_right (measure_mono (self_subset_thickening ?_ B))
    apply ENNReal.toReal_pos
    · refine (@lt_min ℝ≥0∞ _ 0 (ε/2) μ.mass half_ε_pos ?_).ne.symm
      exact ENNReal.coe_pos.mpr (zero_lt_iff.mpr zero_meas)
    · exact (lt_of_le_of_lt (min_le_right _ _) coe_lt_top).ne
  · by_cases ε_infty : ε/2 = ∞
    · convert lt_of_le_of_lt (min_le_right _ _) (coe_lt_top (r := μ.mass))
      rw [(show ε = 2*(ε/2) by rw [ENNReal.mul_div_cancel' two_ne_zero two_ne_top])]
      simp only [ε_infty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_top]
    apply lt_of_le_of_lt (min_le_left _ _)
    simpa only [gt_iff_lt, zero_add, ENNReal.add_halves]
      using ENNReal.add_lt_add_right ε_infty half_ε_pos

lemma LPedist.comm (μ ν : FiniteMeasure Ω) :
    LPedist μ ν = LPedist ν μ := by
  rw [LPedist]
  congr
  ext ε
  simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, mem_setOf_eq]
  refine ⟨?_, ?_⟩ <;>
  · intro h B B_mble
    specialize h B B_mble
    refine ⟨h.2, h.1⟩

lemma LPedist.triangle (μ ν κ : FiniteMeasure Ω) :
    LPedist μ κ ≤ LPedist μ ν + LPedist ν κ := by
  apply LPedist_le_of_forall_add_pos_le
  intro ε B ε_pos ε_lt_top B_mble
  simp only [ne_eq, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at *
  have half_ε_pos : 0 < ε / 2 := by
    simp only [ENNReal.div_pos_iff, ne_eq, ε_pos.ne.symm, not_false_eq_true, two_ne_top, and_self]
  let r := LPedist μ ν + ε / 2
  let s := LPedist ν κ + ε / 2
  have lt_r : LPedist μ ν < r := lt_add_right (LPedist.lt_top μ ν).ne half_ε_pos.ne.symm
  have lt_s : LPedist ν κ < s := lt_add_right (LPedist.lt_top ν κ).ne half_ε_pos.ne.symm
  refine ⟨?_, ?_⟩
  · have obs₁ := left_measure_le_of_LPedist_lt lt_r B_mble
    have mble_B₁ : MeasurableSet (thickening (ENNReal.toReal r) B) :=
      isOpen_thickening.measurableSet
    have obs₂ := left_measure_le_of_LPedist_lt lt_s mble_B₁
    simp only [ENNReal.div_pos_iff, ne_eq, and_true, gt_iff_lt,
      FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ge_iff_le] at *
    apply obs₁.trans
    apply (add_le_add_right obs₂ _).trans
    simp_rw [add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves]
    simp_rw [← add_assoc (LPedist _ _), add_comm (LPedist μ ν) (LPedist ν κ)]
    congr
    apply add_le_add_right (measure_mono _)
    apply (thickening_thickening_subset _ _ _).trans (thickening_mono _ _)
    rw [← ENNReal.toReal_add]
    · simp_rw [add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves, ← add_assoc]
      exact Eq.le rfl
    · simp only [add_ne_top]
      refine ⟨ne_top_of_lt lt_s, (ENNReal.div_lt_top ε_lt_top.ne two_ne_zero).ne⟩
    · simp only [add_ne_top]
      refine ⟨ne_top_of_lt lt_r, (ENNReal.div_lt_top ε_lt_top.ne two_ne_zero).ne⟩
  · have obs₁ := right_measure_le_of_LPedist_lt lt_s B_mble
    have mble_B₁ : MeasurableSet (thickening (ENNReal.toReal s) B) :=
      isOpen_thickening.measurableSet
    have obs₂ := right_measure_le_of_LPedist_lt lt_r mble_B₁
    simp only [ENNReal.div_pos_iff, ne_eq, and_true, gt_iff_lt,
      FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ge_iff_le] at *
    apply obs₁.trans
    apply (add_le_add_right obs₂ _).trans
    simp_rw [add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves]
    simp_rw [← add_assoc (LPedist _ _), add_comm (LPedist μ ν) (LPedist ν κ)]
    congr
    apply add_le_add_right (measure_mono _)
    apply (thickening_thickening_subset _ _ _).trans (thickening_mono _ _)
    rw [← ENNReal.toReal_add]
    · simp_rw [add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves, ← add_assoc]
      rw [add_comm (LPedist _ _)]
    · simp only [add_ne_top]
      refine ⟨ne_top_of_lt lt_r, (ENNReal.div_lt_top ε_lt_top.ne two_ne_zero).ne⟩
    · simp only [add_ne_top]
      refine ⟨ne_top_of_lt lt_s, (ENNReal.div_lt_top ε_lt_top.ne two_ne_zero).ne⟩

/-- The Lévy-Prokhorov distance `LPedist` makes `FiniteMeasure X` a pseudoemetric space. -/
noncomputable def LPedist_pseudoEMetricSpace : PseudoEMetricSpace (FiniteMeasure Ω) where
  edist := LPedist
  edist_self := LPedist.self
  edist_comm := LPedist.comm
  edist_triangle := LPedist.triangle

end Levy_Prokhorov --section
