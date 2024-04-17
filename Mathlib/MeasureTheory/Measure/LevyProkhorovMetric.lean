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

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω]

/-- The Lévy-Prokhorov edistance between measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
noncomputable def levyProkhorovEDist (μ ν : Measure Ω) : ℝ≥0∞ :=
  sInf {ε | ∀ B, MeasurableSet B →
            μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε}

/- This result is not placed in earlier more generic files, since it is rather specialized;
it mixes measure and metric in a very particular way. -/
lemma meas_le_of_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : ℝ≥0∞} (μ ν : Measure Ω)
    (h_le : ε₁ ≤ ε₂) {B : Set Ω} (hε₁ : μ B ≤ ν (thickening ε₁.toReal B) + ε₁) :
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
    simp_rw [s, r, add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves, ← add_assoc,
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

lemma LevyProkhorov.dist_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure ν.toMeasure := rfl

end Levy_Prokhorov --section

section Levy_Prokhorov_comparison

open BoundedContinuousFunction

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- Coercion from the type synonym `LevyProkhorov (ProbabilityMeasure Ω)`
to `ProbabilityMeasure Ω`. -/
def LevyProkhorov.probabilityMeasure (μ : LevyProkhorov (ProbabilityMeasure Ω)) :
    ProbabilityMeasure Ω := μ

/-- Coercion from the type synonym `LevyProkhorov (FiniteMeasure Ω)` to `FiniteMeasure Ω`. -/
def LevyProkhorov.finiteMeasure (μ : LevyProkhorov (FiniteMeasure Ω)) :
    FiniteMeasure Ω := μ

variable [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- A version of the layer cake formula for bounded continuous functions which have finite integral:
∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt. -/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le_of_hasFiniteIntegral
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f) (hf : HasFiniteIntegral f μ) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, ENNReal.toReal (μ {a : α | t ≤ f a}) := by
  rw [Integrable.integral_eq_integral_Ioc_meas_le (M := ‖f‖) ?_ f_nn ?_]
  · exact ⟨f.continuous.measurable.aestronglyMeasurable, hf⟩
  · exact eventually_of_forall (fun x ↦ BoundedContinuousFunction.apply_le_norm f x)

/-- A version of the layer cake formula for bounded continuous functions and finite measures:
∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt. -/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) [IsFiniteMeasure μ] (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, ENNReal.toReal (μ {a : α | t ≤ f a}) :=
  integral_eq_integral_meas_le_of_hasFiniteIntegral _ _ f_nn (f.integrable μ).2

/-- Assuming `levyProkhorovEDist μ ν < ε`, we can bound `∫ f ∂μ` in terms of
`∫ t in (0, ‖f‖], ν (thickening ε {x | f(x) ≥ t}) dt` and `‖f‖`. -/
lemma BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (ε_pos : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ
      ≤ (∫ t in Ioc 0 ‖f‖, ENNReal.toReal (ν (thickening ε {a | t ≤ f a}))) + ε * ‖f‖ := by
  rw [BoundedContinuousFunction.integral_eq_integral_meas_le f μ f_nn]
  have key : (fun (t : ℝ) ↦ ENNReal.toReal (μ {a | t ≤ f a}))
              ≤ (fun (t : ℝ) ↦ ENNReal.toReal (ν (thickening ε {a | t ≤ f a})) + ε) := by
    intro t
    convert (ENNReal.toReal_le_toReal (measure_ne_top _ _) ?_).mpr
            <| left_measure_le_of_levyProkhorovEDist_lt hμν (B := {a | t ≤ f a})
                (f.continuous.measurable measurableSet_Ici)
    · rw [ENNReal.toReal_add (measure_ne_top ν _) ofReal_ne_top, ENNReal.toReal_ofReal ε_pos.le]
    · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, ofReal_ne_top⟩
  have intble₁ : IntegrableOn (fun t ↦ ENNReal.toReal (μ {a | t ≤ f a})) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := ENNReal.toReal (μ univ)) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono (fun _ h ↦ hst.trans h)
    · apply eventually_of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_toReal]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
            <| measure_mono (subset_univ _)
  have intble₂ : IntegrableOn
                  (fun t ↦ ENNReal.toReal (ν (thickening ε {a | t ≤ f a}))) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := ENNReal.toReal (ν univ)) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono <| thickening_subset_of_subset ε (fun _ h ↦ hst.trans h)
    · apply eventually_of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_toReal]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
            <| measure_mono (subset_univ _)
  apply le_trans (set_integral_mono (s := Ioc 0 ‖f‖) ?_ ?_ key)
  rw [integral_add]
  · apply add_le_add_left
    simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
                Real.volume_Ioc, sub_zero, norm_nonneg, toReal_ofReal, smul_eq_mul,
                (mul_comm _ ε).le]
  · exact intble₂
  · exact integrable_const ε
  · exact intble₁
  · exact intble₂.add <| integrable_const ε

/-- A monotone decreasing convergence lemma for integrals of measures of thickenings:
`∫ t in (0, ‖f‖], μ (thickening ε {x | f(x) ≥ t}) dt` tends to
`∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt` as `ε → 0`. -/
lemma tendsto_integral_meas_thickening_le (f : Ω →ᵇ ℝ)
    {A : Set ℝ} (A_finmeas : volume A ≠ ∞) (μ : ProbabilityMeasure Ω) :
    Tendsto (fun ε ↦ ∫ t in A, ENNReal.toReal (μ (thickening ε {a | t ≤ f a}))) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in A, ENNReal.toReal (μ {a | t ≤ f a}))) := by
  apply tendsto_integral_filter_of_dominated_convergence (G := ℝ) (μ := volume.restrict A)
        (F := fun ε t ↦ (μ (thickening ε {a | t ≤ f a}))) (f := fun t ↦ (μ {a | t ≤ f a})) 1
  · apply eventually_of_forall fun n ↦ Measurable.aestronglyMeasurable ?_
    simp only [measurable_coe_nnreal_real_iff]
    apply measurable_toNNReal.comp <| Antitone.measurable (fun s t hst ↦ ?_)
    exact measure_mono <| thickening_subset_of_subset _ <| fun ω h ↦ hst.trans h
  · apply eventually_of_forall (fun i ↦ ?_)
    apply eventually_of_forall (fun t ↦ ?_)
    simp only [Real.norm_eq_abs, NNReal.abs_eq, Pi.one_apply]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) one_ne_top).mpr prob_le_one
  · have aux : IsFiniteMeasure (volume.restrict A) := ⟨by simp [lt_top_iff_ne_top, A_finmeas]⟩
    apply integrable_const
  · apply eventually_of_forall (fun t ↦ ?_)
    simp only [NNReal.tendsto_coe]
    apply (ENNReal.tendsto_toNNReal _).comp
    apply tendsto_measure_thickening_of_isClosed ?_ ?_
    · exact ⟨1, ⟨Real.zero_lt_one, measure_ne_top _ _⟩⟩
    · exact isClosed_le continuous_const f.continuous
    · exact measure_ne_top _ _

/-- The coercion `LevyProkhorov (ProbabilityMeasure Ω) → ProbabilityMeasure Ω` is continuous. -/
lemma continuous_levyProkhorov_to_probabilityMeasure :
    Continuous (LevyProkhorov.probabilityMeasure (Ω := Ω)) := by
  refine SeqContinuous.continuous ?_
  intro μs ν hμs
  set P := ν.probabilityMeasure -- more palatable notation
  set Ps := fun n ↦ (μs n).probabilityMeasure -- more palatable notation
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine fun f ↦ tendsto_integral_of_forall_limsup_integral_le_integral ?_ f
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
    have ε_of_room' : Tendsto (fun n ↦ dist (μs n) ν + εs n) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa using ε_of_room, eventually_of_forall fun n ↦ ?_⟩
      · rw [mem_Ioi]
        linarith [εs_pos n, dist_nonneg (x := μs n) (y := ν)]
    rw [add_zero] at ε_of_room
    have key := (tendsto_integral_meas_thickening_le f (A := Ioc 0 ‖f‖) (by simp) P).comp ε_of_room'
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
        apply (add_le_add_right hn.le _).trans
        rw [BoundedContinuousFunction.integral_eq_integral_meas_le]
        · simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          rw [add_assoc, mul_comm]
          gcongr
          calc
            δ / 2 + ‖f‖ * (dist (μs n) ν + εs n)
            _ ≤ δ / 2 + ‖f‖ * (‖f‖⁻¹ * δ / 2) := by gcongr
            _ = δ := by field_simp; ring
        · exact eventually_of_forall f_nn
      · positivity
      · rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_zero (levyProkhorovEDist _ _)]
        apply ENNReal.add_lt_add_of_le_of_lt (levyProkhorovEDist_ne_top _ _)
              (le_of_eq ?_) (ofReal_pos.mpr εs_pos)
        rw [LevyProkhorov.dist_def, levyProkhorovDist,
            ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
        simp only [Ps, P, LevyProkhorov.probabilityMeasure]
      · exact eventually_of_forall f_nn
  · simp only [IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop,
               ge_iff_le, forall_exists_index]
    exact ⟨0, fun a i hia ↦ le_trans (integral_nonneg f_nn) (hia i rfl.le)⟩

/-- The topology of the Lévy-Prokhorov metric is finer than the topology of convergence in
distribution. -/
theorem levyProkhorov_le_convergenceInDistribution :
    TopologicalSpace.coinduced (LevyProkhorov.probabilityMeasure (Ω := Ω)) inferInstance
      ≤ (inferInstance : TopologicalSpace (ProbabilityMeasure Ω)) :=
  continuous_levyProkhorov_to_probabilityMeasure.coinduced_le

end Levy_Prokhorov_comparison

end MeasureTheory -- namespace
