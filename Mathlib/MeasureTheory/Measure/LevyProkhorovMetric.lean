/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

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

/- This result is not placed in earlier more generic files, since it is rather specialized;
it mixes measure and metric in a very particular way. -/
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
  exact meas_le_of_le_of_forall_le_meas_thickening_add μ ν lt_c.le (hc' B B_mble).1

lemma right_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) :
    ν B ≤ μ (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact meas_le_of_le_of_forall_le_meas_thickening_add ν μ lt_c.le (hc' B B_mble).2

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

-- ...otherwise `exact?` does not find the useful lemma.
lemma levyProkhorovEDist_ne_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν ≠ ∞ := (levyProkhorovEDist_lt_top μ ν).ne

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

lemma levyProkhorov_dist_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure ν.toMeasure := rfl

end Levy_Prokhorov --section

section Levy_Prokhorov_comparison

open BoundedContinuousFunction

variable {ι : Type*} (Ω : Type*) [MeasurableSpace Ω]

def levyProkhorov_to_probabilityMeasure (μ : LevyProkhorov (ProbabilityMeasure Ω)) :
    ProbabilityMeasure Ω := μ

def levyProkhorov_to_finiteMeasure (μ : LevyProkhorov (FiniteMeasure Ω)) :
    FiniteMeasure Ω := μ

variable [MetricSpace Ω] [OpensMeasurableSpace Ω]

example : TopologicalSpace (ProbabilityMeasure Ω) := by exact
  ProbabilityMeasure.instTopologicalSpaceProbabilityMeasure

variable {Ω}

/-
#check lintegral_eq_lintegral_meas_le
#check set_integral_eq_of_subset_of_ae_diff_eq_zero

-- TODO: Add in `MeasureTheory.Integral.SetIntegral`?
/-- If a function vanishes almost everywhere on `t \ s` with `s ⊆ t`, then its (Lebesgue) integrals
on `s` and `t` coincide if `t` is null-measurable. -/
theorem set_lintegral_eq_of_subset_of_ae_diff_eq_zero {α : Type*} [MeasurableSpace α] (f : α → ℝ≥0∞)
    (μ : Measure α) (s t : Set α) (ht : NullMeasurableSet t μ) (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) :
    ∫⁻ x in t, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  sorry

-- TODO: Add to layercake
lemma lintegral_eq_lintegral_Icc_meas_le {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    {M : ℝ} (f_bdd : f ≤ᵐ[μ] (fun _ ↦ M)) (f_mble : AEMeasurable f μ) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioc 0 M, μ {a : α | t ≤ f a} := by
  rw [lintegral_eq_lintegral_meas_le μ f_nn f_mble]
  rw [set_lintegral_eq_of_subset_of_ae_diff_eq_zero _ _ _ _
      measurableSet_Ioi.nullMeasurableSet Ioc_subset_Ioi_self ?_]
  apply eventually_of_forall
  intro t ht
  have htM : M < t := by simp_all only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
  have obs : μ {a | M < f a} = 0 := by
    rw [measure_zero_iff_ae_nmem]
    filter_upwards [f_bdd] with a ha
    exact not_lt.mpr ha
  exact measure_mono_null (fun a ha ↦ lt_of_lt_of_le htM ha) obs

lemma BoundedContinuousFunction.lintegral_eq_lintegral_meas_le {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioc 0 ‖f‖, μ {a : α | t ≤ f a} := by
  rw [@lintegral_eq_lintegral_Icc_meas_le _ _ _ μ f_nn ‖f‖ ?_ f.continuous.measurable.aemeasurable]
  exact eventually_of_forall (fun x ↦ BoundedContinuousFunction.apply_le_norm f x)
 -/

lemma integral_eq_integral_Icc_meas_le {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    {M : ℝ} (f_bdd : f ≤ᵐ[μ] (fun _ ↦ M)) (f_intble : Integrable f μ) :
    (∫ ω, f ω ∂μ) = ∫ t in Ioc 0 M, ENNReal.toReal (μ {a : α | t ≤ f a}) := by
  rw [f_intble.integral_eq_integral_meas_le f_nn]
  rw [set_integral_eq_of_subset_of_ae_diff_eq_zero
      measurableSet_Ioi.nullMeasurableSet Ioc_subset_Ioi_self ?_]
  apply eventually_of_forall
  intro t ht
  have htM : M < t := by simp_all only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
  have obs : μ {a | M < f a} = 0 := by
    rw [measure_zero_iff_ae_nmem]
    filter_upwards [f_bdd] with a ha
    exact not_lt.mpr ha
  rw [toReal_eq_zero_iff]
  exact Or.inl <| measure_mono_null (fun a ha ↦ lt_of_lt_of_le htM ha) obs

lemma BoundedContinuousFunction.integral_eq_integral_meas_le {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f) (hf : HasFiniteIntegral f μ) :
    (∫ ω, f ω ∂μ) = ∫ t in Ioc 0 ‖f‖, ENNReal.toReal (μ {a : α | t ≤ f a}) := by
  rw [integral_eq_integral_Icc_meas_le μ f_nn (M := ‖f‖) ?_ ?_]
  · exact eventually_of_forall (fun x ↦ BoundedContinuousFunction.apply_le_norm f x)
  · refine ⟨f.continuous.measurable.aestronglyMeasurable, hf⟩

lemma BoundedContinuousFunction.integral_eq_integral_meas_le' {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) [IsFiniteMeasure μ] (f_nn : 0 ≤ᵐ[μ] f) :
    (∫ ω, f ω ∂μ) = ∫ t in Ioc 0 ‖f‖, ENNReal.toReal (μ {a : α | t ≤ f a}) :=
  integral_eq_integral_meas_le _ _ f_nn (f.integrable μ).2

lemma integrableOn_of_meas_lt_top_of_norm_le {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    (μ : Measure α) {A : Set α} (A_mble : MeasurableSet A) (A_finite : μ A < ∞)
    {f : α → E} (f_mble : AEStronglyMeasurable f μ)
    {M : ℝ} (f_bdd : ∀ a ∈ A, ‖f a‖ ≤ M) :
    IntegrableOn f A μ := by
  refine ⟨AEStronglyMeasurable.restrict f_mble, ?_⟩
  rw [HasFiniteIntegral]
  have obs : ∫⁻ _ in A, ENNReal.ofReal M ∂μ < ⊤ := by
    rw [lintegral_const]
    apply mul_lt_top ofReal_ne_top
    simpa only [MeasurableSet.univ, Measure.restrict_apply, univ_inter] using A_finite.ne
  apply lt_of_le_of_lt (a := ∫⁻ (a : α) in A, ↑‖f a‖₊ ∂μ) ?_ obs
  apply set_lintegral_mono' A_mble
  intro a a_in_A
  convert ENNReal.ofReal_le_ofReal <| f_bdd a a_in_A
  exact (ofReal_norm_eq_coe_nnnorm (f a)).symm

-- This might be the more useful variant.
lemma BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (ε_pos : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ
      ≤ (∫ t in Ioc 0 ‖f‖, ENNReal.toReal (ν (thickening ε {a | t ≤ f a}))) + ε * ‖f‖ := by
  rw [BoundedContinuousFunction.integral_eq_integral_meas_le' f μ f_nn]
  have key : (fun (t : ℝ) ↦ ENNReal.toReal (μ {a | t ≤ f a}))
              ≤ (fun (t : ℝ) ↦ ENNReal.toReal (ν (thickening ε {a | t ≤ f a})) + ε) := by
    intro t
    convert (ENNReal.toReal_le_toReal (measure_ne_top _ _) ?_).mpr
            <| left_measure_le_of_levyProkhorovEDist_lt hμν (B := {a | t ≤ f a})
                (f.continuous.measurable measurableSet_Ici)
    · rw [ENNReal.toReal_add (measure_ne_top ν _) ofReal_ne_top, ENNReal.toReal_ofReal ε_pos.le]
    · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, ofReal_ne_top⟩
  have intble₁ : IntegrableOn (fun t ↦ ENNReal.toReal (μ {a | t ≤ f a})) (Ioc 0 ‖f‖) := by
    apply integrableOn_of_meas_lt_top_of_norm_le (M := ENNReal.toReal (μ univ)) _
          measurableSet_Ioc measure_Ioc_lt_top
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      apply Antitone.measurable
      exact fun _ _ hst ↦ measure_mono (fun _ h ↦ hst.trans h)
    · intro t _
      simp only [Real.norm_eq_abs, abs_toReal]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
            <| measure_mono (subset_univ _)
  have intble₂ : IntegrableOn (fun t ↦ ENNReal.toReal (ν (thickening ε {a | t ≤ f a}))) (Ioc 0 ‖f‖) := by
    apply integrableOn_of_meas_lt_top_of_norm_le (M := ENNReal.toReal (ν univ)) _
          measurableSet_Ioc measure_Ioc_lt_top
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      apply Antitone.measurable
      exact fun _ _ hst ↦ measure_mono <| thickening_subset_of_subset ε (fun _ h ↦ hst.trans h)
    · intro t _
      simp only [Real.norm_eq_abs, abs_toReal]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
            <| measure_mono (subset_univ _)
  apply le_trans (set_integral_mono (s :=Ioc 0 ‖f‖) ?_ ?_ key)
  rw [integral_add]
  · apply add_le_add rfl.le
    simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
                Real.volume_Ioc, sub_zero, norm_nonneg, toReal_ofReal, smul_eq_mul]
    exact (mul_comm ‖f‖ ε).le
  · exact intble₂
  · exact integrable_const ε
  · exact intble₁
  · exact intble₂.add <| integrable_const ε

lemma tendsto_integral_meas_thickening_le (f : Ω →ᵇ ℝ)
    (εs : ℕ → ℝ) (εs_lim : Tendsto εs atTop (𝓝[>] 0))
    {A : Set ℝ} (A_finmeas : volume A ≠ ∞) (μ : ProbabilityMeasure Ω) :
    Tendsto (fun n ↦ (∫ t in A, ENNReal.toReal (μ (thickening (εs n) {a | t ≤ f a})))) atTop
      (𝓝 (∫ t in A, ENNReal.toReal (μ {a | t ≤ f a}))) := by
  apply tendsto_integral_of_dominated_convergence (G := ℝ) (μ := volume.restrict A)
      (F := fun n t ↦ (μ (thickening (εs n) {a | t ≤ f a}))) (f := fun t ↦ (μ {a | t ≤ f a})) 1
  · apply fun n ↦ Measurable.aestronglyMeasurable ?_
    simp only [measurable_coe_nnreal_real_iff]
    apply measurable_toNNReal.comp <| Antitone.measurable (fun s t hst ↦ ?_)
    exact measure_mono <| thickening_subset_of_subset _ <| fun ω h ↦ hst.trans h
  · have aux : IsFiniteMeasure (volume.restrict A) := ⟨by simp [lt_top_iff_ne_top, A_finmeas]⟩
    apply integrable_const
  · intro n
    apply eventually_of_forall (fun t ↦ ?_)
    simp only [Real.norm_eq_abs, NNReal.abs_eq, Pi.one_apply]
    have obs : (μ.toMeasure (thickening (εs n) {a | t ≤ f a})) ≤ 1 := prob_le_one
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) one_ne_top).mpr obs
  · apply eventually_of_forall (fun t ↦ ?_)
    simp only [NNReal.tendsto_coe]
    apply (ENNReal.tendsto_toNNReal _).comp
    apply (tendsto_measure_thickening_of_isClosed ?_ ?_).comp εs_lim
    · exact ⟨1, ⟨Real.zero_lt_one, measure_ne_top _ _⟩⟩
    · exact isClosed_le continuous_const f.continuous
    · exact measure_ne_top _ _

lemma continuous_levyProkhorov_to_probabilityMeasure :
    Continuous (levyProkhorov_to_probabilityMeasure Ω) := by
  refine SeqContinuous.continuous ?_
  intro μs ν hμs
  set P := levyProkhorov_to_probabilityMeasure Ω ν -- more palatable notation
  set Ps := fun n ↦ levyProkhorov_to_probabilityMeasure Ω (μs n) -- more palatable notation
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine fun f ↦ @tendsto_integral_of_forall_limsup_integral_le_integral Ω _ _ _ ℕ atTop
    P _ (fun n ↦ Ps n) _ ?_ f
  intro f f_nn
  by_cases f_zero : ‖f‖ = 0
  · simp only [norm_eq_zero] at f_zero
    simp [f_zero, limsup_const]
  have norm_f_pos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (fun a => f_zero a.symm)
  apply _root_.le_of_forall_pos_le_add
  intro δ δ_pos
  apply limsup_le_of_le ?_
  · obtain ⟨εs, ⟨_, ⟨εs_pos, εs_lim⟩⟩⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
    have ε_of_room := Tendsto.add (tendsto_iff_dist_tendsto_zero.mp hμs) εs_lim
    rw [add_zero] at ε_of_room
    have key := tendsto_integral_meas_thickening_le f (fun n ↦ dist (μs n) ν + εs n)
                 ?_ (A := Ioc 0 ‖f‖) (by simp) P
    · have aux : ∀ (z : ℝ), Iio (z + δ/2) ∈ 𝓝 z := fun z ↦ Iio_mem_nhds (by linarith)
      filter_upwards [key (aux _), ε_of_room <| Iio_mem_nhds <| half_pos <|
                        Real.mul_pos (inv_pos.mpr norm_f_pos) δ_pos]
        with n hn hn'
      simp only [gt_iff_lt, eventually_atTop, ge_iff_le, ne_eq, mem_map,
        mem_atTop_sets, mem_preimage, mem_Iio] at *
      specialize εs_pos n
      have bound := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt
                      (Ps n) P (ε := dist (μs n) ν + εs n) ?_ ?_ f ?_
      · refine bound.trans ?_
        apply (add_le_add hn.le rfl.le).trans
        rw [BoundedContinuousFunction.integral_eq_integral_meas_le']
        · simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          rw [add_assoc]
          have also : (dist (μs n) ν + εs n) * ‖f‖ ≤ δ/2 := by
            rw [mul_comm]
            apply (mul_le_mul (a := ‖f‖) rfl.le hn'.le
                    (by positivity) (by exact norm_nonneg f)).trans (le_of_eq _)
            field_simp
            ring
          apply add_le_add rfl.le <| (add_le_add rfl.le also).trans <| by linarith
        · exact eventually_of_forall f_nn
      · positivity
      · rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_zero (levyProkhorovEDist _ _)]
        apply ENNReal.add_lt_add_of_le_of_lt (levyProkhorovEDist_ne_top _ _)
              (le_of_eq ?_) (ofReal_pos.mpr εs_pos)
        rw [levyProkhorov_dist_def, levyProkhorovDist,
            ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
        rfl
      · exact eventually_of_forall f_nn
    · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ε_of_room
      apply eventually_of_forall (fun n ↦ ?_)
      simp only [mem_Ioi]
      specialize εs_pos n
      positivity
  · simp only [IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop,
               ge_iff_le, forall_exists_index]
    refine ⟨0, fun a i hia ↦ le_trans (integral_nonneg f_nn) (hia i rfl.le)⟩

theorem levyProkhorov_le_convergenceInDistribution :
    TopologicalSpace.coinduced (levyProkhorov_to_probabilityMeasure Ω) inferInstance
      ≤ (inferInstance : TopologicalSpace (ProbabilityMeasure Ω)) :=
  (continuous_levyProkhorov_to_probabilityMeasure).coinduced_le

end Levy_Prokhorov_comparison

end MeasureTheory -- namespace
