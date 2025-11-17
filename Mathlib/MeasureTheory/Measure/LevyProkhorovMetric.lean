/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# The Lévy-Prokhorov distance on spaces of finite measures and probability measures

## Main definitions

* `MeasureTheory.levyProkhorovEDist`: The Lévy-Prokhorov edistance between two measures.
* `MeasureTheory.levyProkhorovDist`: The Lévy-Prokhorov distance between two finite measures.

## Main results

* `LevyProkhorov.instPseudoMetricSpaceFiniteMeasure`: The Lévy-Prokhorov distance is a
  pseudometric on the space of finite measures.
* `LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure`: The Lévy-Prokhorov distance is a
  pseudometric on the space of probability measures.
* `LevyProkhorov.le_convergenceInDistribution`: The topology of the Lévy-Prokhorov metric on
  probability measures is always at least as fine as the topology of convergence in distribution.
* `LevyProkhorov.eq_convergenceInDistribution`: The topology of the Lévy-Prokhorov metric on
  probability measures on a separable space coincides with the topology of convergence in
  distribution, and in particular convergence in distribution is then pseudometrizable.

## Tags

finite measure, probability measure, weak convergence, convergence in distribution, metrizability
-/

@[expose] public section

open Topology Metric Filter Set ENNReal NNReal

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Levy_Prokhorov

/-! ### Lévy-Prokhorov metric -/

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω]

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
  · simp only [ε_top, toReal_top,
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

/-- A general sufficient condition for bounding `levyProkhorovEDist` from above. -/
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
  simpa only [add_assoc] using h ε B (by positivity) coe_lt_top B_mble

/-- A simple general sufficient condition for bounding `levyProkhorovEDist` from above. -/
lemma levyProkhorovEDist_le_of_forall (μ ν : Measure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B →
        μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  by_cases δ_top : δ = ∞
  · simp only [δ_top, le_top]
  apply levyProkhorovEDist_le_of_forall_add_pos_le
  intro x B x_pos x_lt_top B_mble
  simpa only [← add_assoc] using h (δ + x) B (ENNReal.lt_add_right δ_top x_pos.ne.symm)
    (by simp only [add_lt_top, Ne.lt_top δ_top, x_lt_top, and_self]) B_mble

lemma levyProkhorovEDist_le_max_measure_univ (μ ν : Measure Ω) :
    levyProkhorovEDist μ ν ≤ max (μ univ) (ν univ) := by
  refine sInf_le fun B _ ↦ ⟨?_, ?_⟩ <;> apply le_add_left <;> simp [measure_mono]

@[simp] lemma levyProkhorovEDist_lt_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν < ∞ :=
  (levyProkhorovEDist_le_max_measure_univ μ ν).trans_lt <| by simp [measure_lt_top]

@[simp] lemma levyProkhorovEDist_ne_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν ≠ ∞ := (levyProkhorovEDist_lt_top μ ν).ne

@[simp] lemma levyProkhorovEDist_self (μ : Measure Ω) : levyProkhorovEDist μ μ = 0 := by
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
  have half_ε_pos : 0 < ε / 2 := ENNReal.div_pos ε_pos.ne' ofNat_ne_top
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
    · finiteness
    · finiteness
  rw [← hs_add_r', add_assoc, ← hs_add_r, add_assoc _ _ ε, ← hs_add_r]
  refine ⟨?_, ?_⟩
  · calc μ B ≤ ν (thickening r.toReal B) + r :=
      left_measure_le_of_levyProkhorovEDist_lt lt_r B_mble
    _ ≤ κ (thickening s.toReal (thickening r.toReal B)) + s + r := by
      grw [left_measure_le_of_levyProkhorovEDist_lt lt_s isOpen_thickening.measurableSet]
    _ = κ (thickening s.toReal (thickening r.toReal B)) + (s + r) := add_assoc _ _ _
    _ ≤ κ (thickening (s.toReal + r.toReal) B) + (s + r) := by grw [thickening_thickening_subset]
  · calc κ B ≤ ν (thickening s.toReal B) + s :=
      right_measure_le_of_levyProkhorovEDist_lt lt_s B_mble
    _ ≤ μ (thickening r.toReal (thickening s.toReal B)) + r + s := by
      grw [right_measure_le_of_levyProkhorovEDist_lt lt_r isOpen_thickening.measurableSet]
    _ = μ (thickening r.toReal (thickening s.toReal B)) + (s + r) := by rw [add_assoc, add_comm r]
    _ ≤ μ (thickening (r.toReal + s.toReal) B) + (s + r) := by grw [thickening_thickening_subset]
    _ = μ (thickening (s.toReal + r.toReal) B) + (s + r) := by rw [add_comm r.toReal]

/-- The Lévy-Prokhorov distance between finite measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
noncomputable def levyProkhorovDist (μ ν : Measure Ω) : ℝ :=
  (levyProkhorovEDist μ ν).toReal

lemma levyProkhorovDist_self (μ : Measure Ω) :
    levyProkhorovDist μ μ = 0 := by
  simp only [levyProkhorovDist, levyProkhorovEDist_self, toReal_zero]

lemma levyProkhorovDist_comm (μ ν : Measure Ω) :
    levyProkhorovDist μ ν = levyProkhorovDist ν μ := by
  simp only [levyProkhorovDist, levyProkhorovEDist_comm]

lemma levyProkhorovDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    levyProkhorovDist μ κ ≤ levyProkhorovDist μ ν + levyProkhorovDist ν κ := by
  have dμν_finite := (levyProkhorovEDist_lt_top μ ν).ne
  have dνκ_finite := (levyProkhorovEDist_lt_top ν κ).ne
  convert ENNReal.toReal_mono ?_ <| levyProkhorovEDist_triangle μ ν κ
  · simp only [levyProkhorovDist, ENNReal.toReal_add dμν_finite dνκ_finite]
  · exact ENNReal.add_ne_top.mpr ⟨dμν_finite, dνκ_finite⟩

variable [OpensMeasurableSpace Ω]

lemma measure_le_measure_closure_of_levyProkhorovEDist_eq_zero {μ ν : Measure Ω}
    (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_mble : MeasurableSet s)
    (h_finite : ∃ δ > 0, ν (thickening δ s) ≠ ∞) :
    μ s ≤ ν (closure s) := by
  have key : Tendsto (fun ε ↦ ν (thickening ε.toReal s)) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 (ν (closure s))) := by
    have aux : Tendsto ENNReal.toReal (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (s := Ioi 0) ENNReal.toReal
      · exact tendsto_nhdsWithin_of_tendsto_nhds (continuousAt_toReal zero_ne_top).tendsto
      · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
        exact toReal_pos hx.1.ne' <| ne_top_of_lt hx.2
    exact (tendsto_measure_thickening h_finite).comp aux
  have obs := Tendsto.add key (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  simp only [id_eq, add_zero] at obs
  apply ge_of_tendsto (b := μ s) obs
  filter_upwards [self_mem_nhdsWithin] with ε ε_pos
  exact left_measure_le_of_levyProkhorovEDist_lt (B_mble := s_mble) (hLP ▸ ε_pos)

/-- Two measures at vanishing Lévy-Prokhorov distance from each other assign the same values to all
closed sets. -/
lemma measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed {μ ν : Measure Ω}
    (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_closed : IsClosed s)
    (hμs : ∃ δ > 0, μ (thickening δ s) ≠ ∞) (hνs : ∃ δ > 0, ν (thickening δ s) ≠ ∞) :
    μ s = ν s := by
  apply le_antisymm
  · exact measure_le_measure_closure_of_levyProkhorovEDist_eq_zero
      hLP s_closed.measurableSet hνs |>.trans <|
      le_of_eq (congr_arg _ s_closed.closure_eq)
  · exact measure_le_measure_closure_of_levyProkhorovEDist_eq_zero
      (levyProkhorovEDist_comm μ ν ▸ hLP) s_closed.measurableSet hμs |>.trans <|
      le_of_eq (congr_arg _ s_closed.closure_eq)

/-- A simple sufficient condition for bounding `levyProkhorovEDist` between probability measures
from above. The condition involves only one of two natural bounds, the other bound is for free. -/
lemma levyProkhorovEDist_le_of_forall_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B → μ B ≤ ν (thickening ε.toReal B) + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  apply levyProkhorovEDist_le_of_forall μ ν δ
  intro ε B ε_gt ε_lt_top B_mble
  refine ⟨h ε B ε_gt ε_lt_top B_mble, ?_⟩
  have B_subset := subset_compl_thickening_compl_thickening_self ε.toReal B
  apply (measure_mono (μ := ν) B_subset).trans
  rw [prob_compl_eq_one_sub isOpen_thickening.measurableSet]
  have Tc_mble := (isOpen_thickening (δ := ε.toReal) (E := B)).isClosed_compl.measurableSet
  specialize h ε (thickening ε.toReal B)ᶜ ε_gt ε_lt_top Tc_mble
  rw [prob_compl_eq_one_sub isOpen_thickening.measurableSet] at h
  have almost := add_le_add (c := μ (thickening ε.toReal B)) h rfl.le
  rw [tsub_add_cancel_of_le prob_le_one, add_assoc] at almost
  apply (tsub_le_tsub_right almost _).trans
  rw [ENNReal.add_sub_cancel_left (measure_ne_top ν _), add_comm ε]

/-- A simple sufficient condition for bounding `levyProkhorovDist` between probability measures
from above. The condition involves only one of two natural bounds, the other bound is for free. -/
lemma levyProkhorovDist_le_of_forall_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ} (δ_nn : 0 ≤ δ)
    (h : ∀ ε B, δ < ε → MeasurableSet B → μ B ≤ ν (thickening ε B) + ENNReal.ofReal ε) :
    levyProkhorovDist μ ν ≤ δ := by
  apply toReal_le_of_le_ofReal δ_nn
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B ε_gt ε_lt_top B_mble
  have ε_gt' : δ < ε.toReal := by
    refine (ofReal_lt_ofReal_iff ?_).mp ?_
    · exact ENNReal.toReal_pos ε_gt.bot_lt.ne' ε_lt_top.ne
    · simpa [ofReal_toReal_eq_iff.mpr ε_lt_top.ne] using ε_gt
  convert h ε.toReal B ε_gt' B_mble
  exact (ENNReal.ofReal_toReal ε_lt_top.ne).symm

/-! ### Equipping measures with the Lévy-Prokhorov metric -/

/-- A type synonym, to be used for `Measure α`, `FiniteMeasure α`, or `ProbabilityMeasure α`,
when they are to be equipped with the Lévy-Prokhorov distance. -/
structure LevyProkhorov (α : Type*) where
  /-- Turn a measure into the corresponding element of the space of measures equipped with the
  Lévy-Prokhorov metric. -/
  ofMeasure ::
  /-- Turn an element of the space of measure equipped with the Lévy-Prokhorov metric into the
  corresponding measure. -/
  toMeasure : α

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `ofMeasure x` being printed as `{ toMeasure := x }` by `delabStructureInstance`.
-/
@[app_delab LevyProkhorov.ofMeasure]
meta def LevyProkhorov.delabOfMeasure : Delab := delabApp

namespace LevyProkhorov

lemma toMeasure_injective {α : Type*} : (toMeasure : LevyProkhorov α → α).Injective :=
  fun ⟨μ⟩ ⟨ν⟩ => by congr!

/-- `LevyProkhorov.toMeasure` as an equiv. -/
@[simps]
def toMeasureEquiv {α : Type*} : LevyProkhorov α ≃ α where
  toFun := toMeasure
  invFun := ofMeasure

@[deprecated (since := "2025-10-28")] alias equiv := toMeasureEquiv

/-- The Lévy-Prokhorov distance `levyProkhorovEDist` makes `Measure Ω` a pseudoemetric
space. The instance is recorded on the type synonym `LevyProkhorov (Measure Ω) := Measure Ω`. -/
noncomputable instance instPseudoEMetricSpaceMeasure :
    PseudoEMetricSpace (LevyProkhorov (Measure Ω)) where
  edist μ ν := levyProkhorovEDist μ.toMeasure ν.toMeasure
  edist_self _ := levyProkhorovEDist_self _
  edist_comm _ _ := levyProkhorovEDist_comm ..
  edist_triangle _ _ _ := levyProkhorovEDist_triangle ..

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `FiniteMeasure Ω` a pseudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (FiniteMeasure Ω) := FiniteMeasure Ω`. -/
noncomputable instance instPseudoMetricSpaceFiniteMeasure :
    PseudoMetricSpace (LevyProkhorov (FiniteMeasure Ω)) where
  edist μ ν := levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
  dist μ ν := levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
  dist_self _ := levyProkhorovDist_self _
  dist_comm _ _ := levyProkhorovDist_comm ..
  dist_triangle _ _ _ := levyProkhorovDist_triangle ..
  edist_dist μ ν := by simp [levyProkhorovDist, levyProkhorovEDist_ne_top]

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `ProbabilityMeasure Ω` a pseudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this pseudometric to give the topology of convergence in distribution, one must
furthermore assume that `Ω` is separable. -/
noncomputable instance instPseudoMetricSpaceProbabilityMeasure :
    PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) :=
  .induced (LevyProkhorov.ofMeasure ·.toMeasure.toFiniteMeasure) inferInstance

lemma edist_measure_def (μ ν : LevyProkhorov (Measure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure ν.toMeasure := rfl

lemma edist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl

lemma dist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl

lemma edist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl

lemma dist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl

@[deprecated (since := "2025-10-28")] alias dist_def := dist_probabilityMeasure_def

/-- If `Ω` is a Borel space, then the Lévy-Prokhorov distance `levyProkhorovDist` makes
`ProbabilityMeasure Ω` into a metric space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this metric to give the topology of convergence in distribution, one must
furthermore assume that `Ω` is separable. -/
noncomputable instance levyProkhorovDist_metricSpace_probabilityMeasure [BorelSpace Ω] :
    MetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) where
  eq_of_dist_eq_zero {μ ν} h := by
    apply toMeasure_injective
    apply ProbabilityMeasure.toMeasure_injective
    refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun A hA ↦ ?_) (by simp)
    · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]
    refine measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed ?_ hA ?_ ?_
    · simpa [dist_probabilityMeasure_def, levyProkhorovDist, toReal_eq_zero_iff] using h
    · exact ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩
    · exact ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩

end LevyProkhorov
end Levy_Prokhorov --section

section Levy_Prokhorov_is_finer

/-! ### The Lévy-Prokhorov topology is at least as fine as convergence in distribution -/

open BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω]

variable [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- A version of the layer cake formula for bounded continuous functions which have finite integral:
∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt. -/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le_of_hasFiniteIntegral
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f) (hf : HasFiniteIntegral f μ) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, μ.real {a : α | t ≤ f a} := by
  rw [Integrable.integral_eq_integral_Ioc_meas_le (M := ‖f‖) ?_ f_nn ?_]
  · exact ⟨f.continuous.measurable.aestronglyMeasurable, hf⟩
  · exact Eventually.of_forall (fun x ↦ BoundedContinuousFunction.apply_le_norm f x)

/-- A version of the layer cake formula for bounded continuous functions and finite measures:
∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt. -/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) [IsFiniteMeasure μ] (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, μ.real {a : α | t ≤ f a} :=
  integral_eq_integral_meas_le_of_hasFiniteIntegral _ _ f_nn (f.integrable μ).2

/-- Assuming `levyProkhorovEDist μ ν < ε`, we can bound `∫ f ∂μ` in terms of
`∫ t in (0, ‖f‖], ν (thickening ε {x | f(x) ≥ t}) dt` and `‖f‖`. -/
lemma BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (ε_pos : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ
      ≤ (∫ t in Ioc 0 ‖f‖, ν.real (thickening ε {a | t ≤ f a})) + ε * ‖f‖ := by
  rw [BoundedContinuousFunction.integral_eq_integral_meas_le f μ f_nn]
  have key : (fun (t : ℝ) ↦ μ.real {a | t ≤ f a})
              ≤ (fun (t : ℝ) ↦ ν.real (thickening ε {a | t ≤ f a}) + ε) := by
    intro t
    simp only [measureReal_def]
    convert ENNReal.toReal_mono ?_ <| left_measure_le_of_levyProkhorovEDist_lt hμν
      (B := {a | t ≤ f a}) (f.continuous.measurable measurableSet_Ici)
    · rw [ENNReal.toReal_add (measure_ne_top ν _) ofReal_ne_top, ENNReal.toReal_ofReal ε_pos.le]
    · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, ofReal_ne_top⟩
  have intble₁ : IntegrableOn (fun t ↦ μ.real {a | t ≤ f a}) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := μ.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (subset_univ _)
  have intble₂ : IntegrableOn (fun t ↦ ν.real (thickening ε {a | t ≤ f a})) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := ν.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono <| thickening_subset_of_subset ε (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact ENNReal.toReal_mono (by finiteness) <| measure_mono (subset_univ _)
  apply le_trans (setIntegral_mono (s := Ioc 0 ‖f‖) ?_ ?_ key)
  · rw [integral_add]
    · simp [(mul_comm _ ε).le]
    · exact intble₂
    · exact integrable_const ε
  · exact intble₁
  · exact intble₂.add <| integrable_const ε

/-- A monotone decreasing convergence lemma for integrals of measures of thickenings:
`∫ t in (0, ‖f‖], μ (thickening ε {x | f(x) ≥ t}) dt` tends to
`∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt` as `ε → 0`. -/
lemma tendsto_integral_meas_thickening_le (f : Ω →ᵇ ℝ)
    {A : Set ℝ} (A_finmeas : volume A ≠ ∞) (μ : ProbabilityMeasure Ω) :
    Tendsto (fun ε ↦ ∫ t in A, (Measure.real μ (thickening ε {a | t ≤ f a}))) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in A, (Measure.real μ {a | t ≤ f a}))) := by
  apply tendsto_integral_filter_of_dominated_convergence (G := ℝ) (μ := volume.restrict A)
        (F := fun ε t ↦ (μ (thickening ε {a | t ≤ f a}))) (f := fun t ↦ (μ {a | t ≤ f a})) 1
  · apply Eventually.of_forall fun n ↦ Measurable.aestronglyMeasurable ?_
    simp only [measurable_coe_nnreal_real_iff]
    apply measurable_toNNReal.comp <| Antitone.measurable (fun s t hst ↦ ?_)
    exact measure_mono <| thickening_subset_of_subset _ <| fun ω h ↦ hst.trans h
  · apply Eventually.of_forall (fun i ↦ ?_)
    apply Eventually.of_forall (fun t ↦ ?_)
    simp only [Real.norm_eq_abs, NNReal.abs_eq, Pi.one_apply]
    exact ENNReal.toReal_mono one_ne_top prob_le_one
  · have aux : IsFiniteMeasure (volume.restrict A) := ⟨by simp [lt_top_iff_ne_top, A_finmeas]⟩
    apply integrable_const
  · apply Eventually.of_forall (fun t ↦ ?_)
    simp only [NNReal.tendsto_coe]
    apply (ENNReal.tendsto_toNNReal _).comp
    · apply tendsto_measure_thickening_of_isClosed ?_ ?_
      · exact ⟨1, ⟨Real.zero_lt_one, measure_ne_top _ _⟩⟩
      · exact isClosed_le continuous_const f.continuous
    · finiteness

/-- The identity map `LevyProkhorov (ProbabilityMeasure Ω) → ProbabilityMeasure Ω` is continuous. -/
lemma LevyProkhorov.continuous_toMeasure_probabilityMeasure :
    Continuous (toMeasure (α := ProbabilityMeasure Ω)) := by
  refine SeqContinuous.continuous ?_
  intro μs ν hμs
  set P := ν.toMeasure -- more palatable notation
  set Ps := LevyProkhorov.toMeasure ∘ μs -- more palatable notation
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
  · obtain ⟨εs, _, εs_pos, εs_lim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
    have ε_of_room := Tendsto.add (tendsto_iff_dist_tendsto_zero.mp hμs) εs_lim
    have ε_of_room' : Tendsto (fun n ↦ dist (μs n) ν + εs n) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa using ε_of_room, Eventually.of_forall fun n ↦ ?_⟩
      · rw [mem_Ioi]
        linarith [εs_pos n, dist_nonneg (x := μs n) (y := ν)]
    rw [add_zero] at ε_of_room
    have key := (tendsto_integral_meas_thickening_le f (A := Ioc 0 ‖f‖) (by simp) P).comp ε_of_room'
    have aux : ∀ (z : ℝ), Iio (z + δ/2) ∈ 𝓝 z := fun z ↦ Iio_mem_nhds (by linarith)
    filter_upwards [key (aux _), ε_of_room <| Iio_mem_nhds <| half_pos <|
                      mul_pos (inv_pos.mpr norm_f_pos) δ_pos]
      with n hn hn'
    simp only [mem_preimage, Function.comp_def, mem_Iio] at *
    specialize εs_pos n
    have bound := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt
                    (Ps n) P (ε := dist (μs n) ν + εs n) ?_ ?_ f ?_
    · grw [bound, hn, BoundedContinuousFunction.integral_eq_integral_meas_le _ _ <| .of_forall f_nn,
        add_assoc, mul_comm]
      gcongr
      calc
        δ / 2 + ‖f‖ * (dist (μs n) ν + εs n)
        _ ≤ δ / 2 + ‖f‖ * (‖f‖⁻¹ * δ / 2) := by gcongr
        _ = δ := by field
    · positivity
    · rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_zero (levyProkhorovEDist _ _)]
      apply ENNReal.add_lt_add_of_le_of_lt (levyProkhorovEDist_ne_top _ _)
            (le_of_eq ?_) (ofReal_pos.mpr εs_pos)
      rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist,
        ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
      rfl
    · exact Eventually.of_forall f_nn
  · simp only [IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop,
               forall_exists_index]
    refine ⟨0, fun a i hia ↦ le_trans (integral_nonneg f_nn) (hia i le_rfl)⟩

@[deprecated (since := "2025-10-28")]
alias LevyProkhorov.continuous_equiv_probabilityMeasure :=
  LevyProkhorov.continuous_toMeasure_probabilityMeasure

/-- The topology of the Lévy-Prokhorov metric is at least as fine as the topology of convergence in
distribution. -/
theorem LevyProkhorov.le_convergenceInDistribution :
    TopologicalSpace.coinduced (LevyProkhorov.toMeasure (α := ProbabilityMeasure Ω)) inferInstance
      ≤ (inferInstance : TopologicalSpace (ProbabilityMeasure Ω)) :=
  LevyProkhorov.continuous_toMeasure_probabilityMeasure.coinduced_le

@[deprecated (since := "2025-10-28")]
alias _root_.MeasureTheory.levyProkhorov_le_convergenceInDistribution :=
  LevyProkhorov.le_convergenceInDistribution

end Levy_Prokhorov_is_finer

section Levy_Prokhorov_metrizes_convergence_in_distribution

/-! ### On separable spaces the Lévy-Prokhorov distance metrizes convergence in distribution -/

open BoundedContinuousFunction TopologicalSpace

variable {Ω : Type*} [PseudoMetricSpace Ω]
variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

lemma ProbabilityMeasure.toMeasure_add_pos_gt_mem_nhds (P : ProbabilityMeasure Ω)
    {G : Set Ω} (G_open : IsOpen G) {ε : ℝ≥0∞} (ε_pos : 0 < ε) :
    {Q | P.toMeasure G < Q.toMeasure G + ε} ∈ 𝓝 P := by
  by_cases! easy : P.toMeasure G < ε
  · exact Eventually.of_forall (fun _ ↦ lt_of_lt_of_le easy le_add_self)
  by_cases ε_top : ε = ∞
  · simp [ε_top, measure_lt_top]
  have aux : P.toMeasure G - ε < liminf (fun Q ↦ Q.toMeasure G) (𝓝 P) := by
    apply lt_of_lt_of_le (ENNReal.sub_lt_self (by finiteness) _ _)
        <| ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id G_open
    · exact (lt_of_lt_of_le ε_pos easy).ne.symm
    · exact ε_pos.ne.symm
  filter_upwards [gt_mem_sets_of_limsInf_gt (α := ℝ≥0∞) isBounded_ge_of_bot
      (show P.toMeasure G - ε < limsInf ((𝓝 P).map (fun Q ↦ Q.toMeasure G)) from aux)] with Q hQ
  simp only [preimage_setOf_eq, mem_setOf_eq] at hQ
  convert ENNReal.add_lt_add_right ε_top hQ
  exact (tsub_add_cancel_of_le easy).symm

variable [SeparableSpace Ω]

variable (Ω) in
/-- In a separable pseudometric space, for any ε > 0 there exists a countable collection of
disjoint Borel measurable subsets of diameter at most ε that cover the whole space. -/
lemma SeparableSpace.exists_measurable_partition_diam_le {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (As : ℕ → Set Ω), (∀ n, MeasurableSet (As n)) ∧ (∀ n, Bornology.IsBounded (As n)) ∧
        (∀ n, diam (As n) ≤ ε) ∧ (⋃ n, As n = univ) ∧
        (Pairwise (fun (n m : ℕ) ↦ Disjoint (As n) (As m))) := by
  cases isEmpty_or_nonempty Ω
  · refine ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ ↦ Bornology.isBounded_empty, ?_, ?_,
            fun _ _ _ ↦ disjoint_of_subsingleton⟩
    · intro n
      simpa only [diam_empty] using ε_pos.le
    · subsingleton
  obtain ⟨xs, xs_dense⟩ := exists_dense_seq Ω
  have half_ε_pos : 0 < ε / 2 := half_pos ε_pos
  set Bs := fun n ↦ Metric.ball (xs n) (ε / 2)
  set As := disjointed Bs
  refine ⟨As, ?_, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.disjointed (fun n ↦ measurableSet_ball)
  · exact fun n ↦ Bornology.IsBounded.subset isBounded_ball <| disjointed_subset Bs n
  · intro n
    apply (diam_mono (disjointed_subset Bs n) isBounded_ball).trans
    convert diam_ball half_ε_pos.le
    ring
  · have aux : ⋃ n, Bs n = univ := by
      convert DenseRange.iUnion_uniformity_ball xs_dense <| Metric.dist_mem_uniformity half_ε_pos
      exact (ball_eq_ball' _ _).symm
    simpa only [← aux] using iUnion_disjointed
  · exact disjoint_disjointed Bs

namespace LevyProkhorov

lemma continuous_ofMeasure_probabilityMeasure :
    Continuous (ofMeasure (α := ProbabilityMeasure Ω)) := by
  -- We check continuity of `id : ProbabilityMeasure Ω → LevyProkhorov (ProbabilityMeasure Ω)` at
  -- each point `P : ProbabilityMeasure Ω`.
  rw [continuous_iff_continuousAt]
  intro P
  -- To check continuity, fix `ε > 0`. To leave some wiggle room, be ready to use `ε/3 > 0` instead.
  rw [continuousAt_iff']
  intro ε ε_pos
  have third_ε_pos : 0 < ε / 3 := by linarith
  have third_ε_pos' : 0 < ENNReal.ofReal (ε / 3) := ofReal_pos.mpr third_ε_pos
  -- First use separability to choose a countable partition of `Ω` into measurable
  -- subsets `Es n ⊆ Ω` of small diameter, `diam (Es n) < ε/3`.
  obtain ⟨Es, Es_mble, Es_bdd, Es_diam, Es_cover, Es_disjoint⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le Ω third_ε_pos
  -- Instead of the whole space `Ω = ⋃ n ∈ ℕ, Es n`, focus on a large but finite
  -- union `⋃ n < N, Es n`, chosen in such a way that the complement has small `P`-mass,
  -- `P (⋃ n < N, Es n)ᶜ < ε/3`.
  obtain ⟨N, hN⟩ : ∃ N, P.toMeasure (⋃ j ∈ Iio N, Es j)ᶜ < ENNReal.ofReal (ε/3) := by
    have exhaust := @tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint Ω _ P.toMeasure _
                    Es (fun n ↦ (Es_mble n).nullMeasurableSet) Es_disjoint
    simp only [tendsto_atTop_nhds, Function.comp_apply] at exhaust
    obtain ⟨N, hN⟩ := exhaust (Iio (ENNReal.ofReal (ε / 3))) third_ε_pos' isOpen_Iio
    refine ⟨N, ?_⟩
    have rewr : ⋃ i, ⋃ (_ : N ≤ i), Es i = (⋃ i, ⋃ (_ : i < N), Es i)ᶜ := by
      simpa only [mem_Iio, compl_Iio, mem_Ici] using
        (biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ Es_cover Es_disjoint (Iio N)).symm
    simpa only [mem_Iio, ← rewr, gt_iff_lt] using hN N le_rfl
  -- With the finite `N` fixed above, consider the finite collection of open sets of the form
  -- `Gs J = thickening (ε/3) (⋃ j ∈ J, Es j)`, where `J ⊆ {0, 1, ..., N-1}`.
  have Js_finite : Set.Finite {J | J ⊆ Iio N} := Finite.finite_subsets <| finite_Iio N
  set Gs := (fun (J : Set ℕ) ↦ thickening (ε/3) (⋃ j ∈ J, Es j)) '' {J | J ⊆ Iio N}
  have Gs_open : ∀ (J : Set ℕ), IsOpen (thickening (ε/3) (⋃ j ∈ J, Es j)) :=
    fun J ↦ isOpen_thickening
  -- Any open set `G ⊆ Ω` determines a neighborhood of `P` consisting of those `Q` that
  -- satisfy `P G < Q G + ε/3`.
  have mem_nhds_P (G : Set Ω) (G_open : IsOpen G) :
      {Q | P.toMeasure G < Q.toMeasure G + ENNReal.ofReal (ε/3)} ∈ 𝓝 P :=
    P.toMeasure_add_pos_gt_mem_nhds G_open third_ε_pos'
  -- Assume that `Q` is in the neighborhood of `P` such that for each `J ⊆ {0, 1, ..., N-1}`
  -- we have `P (Gs J) < Q (Gs J) + ε/3`.
  filter_upwards [(Finset.iInter_mem_sets Js_finite.toFinset).mpr <|
                    fun J _ ↦ mem_nhds_P _ (Gs_open J)] with Q hQ
  simp only [Finite.mem_toFinset, mem_setOf_eq, thickening_iUnion, mem_iInter] at hQ
  -- Note that in order to show that the Lévy-Prokhorov distance between `P` and `Q` is small
  -- (`≤ 2*ε/3`), it suffices to show that for arbitrary subsets `B ⊆ Ω`, the measure `P B` is
  -- bounded above up to a small error by the `Q`-measure of a small thickening of `B`.
  apply lt_of_le_of_lt ?_ (show 2*(ε/3) < ε by linarith)
  rw [dist_comm, dist_probabilityMeasure_def]
  -- Fix an arbitrary set `B ⊆ Ω`, and an arbitrary `δ > 2*ε/3` to gain some room for error
  -- and for thickening.
  apply levyProkhorovDist_le_of_forall_le _ _ (by linarith) (fun δ B δ_gt _ ↦ ?_)
  -- Let `JB ⊆ {0, 1, ..., N-1}` consist of those indices `j` such that `B` intersects `Es j`.
  -- Then the open set `Gs JB` approximates `B` rather well:
  -- except for what happens in the small complement `(⋃ n < N, Es n)ᶜ`, the set `B` is
  -- contained in `Gs JB`, and conversely `Gs JB` only contains points within `δ` from `B`.
  set JB := {i | B ∩ Es i ≠ ∅ ∧ i ∈ Iio N}
  have B_subset : B ⊆ (⋃ i ∈ JB, thickening (ε/3) (Es i)) ∪ (⋃ j ∈ Iio N, Es j)ᶜ := by
    suffices B ⊆ (⋃ i ∈ JB, thickening (ε/3) (Es i)) ∪ (⋃ j ∈ Ici N, Es j) by
      refine this.trans <| union_subset_union le_rfl ?_
      intro ω hω
      simp only [mem_Ici, mem_iUnion, exists_prop] at hω
      obtain ⟨i, i_large, ω_in_Esi⟩ := hω
      by_contra con
      simp only [mem_Iio, compl_iUnion, mem_iInter, mem_compl_iff, not_forall, not_not,
                  exists_prop] at con
      obtain ⟨j, j_small, ω_in_Esj⟩ := con
      exact disjoint_left.mp (Es_disjoint (show j ≠ i by cutsat)) ω_in_Esj ω_in_Esi
    intro ω ω_in_B
    obtain ⟨i, hi⟩ := show ∃ n, ω ∈ Es n by simp only [← mem_iUnion, Es_cover, mem_univ]
    simp only [mem_Ici, mem_union, mem_iUnion, exists_prop]
    by_cases i_small : i ∈ Iio N
    · refine Or.inl ⟨i, ?_, self_subset_thickening third_ε_pos _ hi⟩
      simp only [mem_Iio, mem_setOf_eq, JB]
      push_neg
      exact ⟨Set.nonempty_of_mem <| mem_inter ω_in_B hi, i_small⟩
    · exact Or.inr ⟨i, by simpa only [mem_Iio, not_lt] using i_small, hi⟩
  have subset_thickB : ⋃ i ∈ JB, thickening (ε / 3) (Es i) ⊆ thickening δ B := by
    intro ω ω_in_U
    simp only [mem_iUnion, exists_prop] at ω_in_U
    obtain ⟨k, ⟨B_intersects, _⟩, ω_in_thEk⟩ := ω_in_U
    rw [mem_thickening_iff] at ω_in_thEk ⊢
    obtain ⟨w, w_in_Ek, w_near⟩ := ω_in_thEk
    obtain ⟨z, ⟨z_in_B, z_in_Ek⟩⟩ := nonempty_iff_ne_empty.mpr B_intersects
    refine ⟨z, z_in_B, lt_of_le_of_lt (dist_triangle ω w z) ?_⟩
    apply lt_of_le_of_lt (add_le_add w_near.le <|
            (dist_le_diam_of_mem (Es_bdd k) w_in_Ek z_in_Ek).trans <| Es_diam k)
    linarith
  -- We use the resulting upper bound `P B ≤ P (Gs JB) + P (small complement)`.
  apply (measure_mono B_subset).trans ((measure_union_le _ _).trans ?_)
  -- From the choice of `Q` in a suitable neighborhood, we have `P (Gs JB) < Q (Gs JB) + ε/3`.
  specialize hQ _ (show JB ⊆ Iio N from fun _ h ↦ h.2)
  -- Now it remains to add the pieces and use the above estimates.
  apply (add_le_add hQ.le hN.le).trans
  rw [add_assoc, ← ENNReal.ofReal_add third_ε_pos.le third_ε_pos.le, ← two_mul]
  apply add_le_add (measure_mono subset_thickB) (ofReal_le_ofReal _)
  exact δ_gt.le

@[deprecated (since := "2025-10-28")]
alias continuous_equiv_symm_probabilityMeasure := continuous_ofMeasure_probabilityMeasure

/-- The topology of the Lévy-Prokhorov metric on probability measures on a separable space
coincides with the topology of convergence in distribution. -/
theorem eq_convergenceInDistribution :
    (inferInstance : TopologicalSpace (ProbabilityMeasure Ω))
      = TopologicalSpace.coinduced LevyProkhorov.toMeasure inferInstance :=
  le_convergenceInDistribution.antisymm' fun s hs ↦ by
    simpa using hs.preimage continuous_ofMeasure_probabilityMeasure

@[deprecated (since := "2025-10-28")]
alias _root_.MeasureTheory.levyProkhorov_eq_convergenceInDistribution :=
 eq_convergenceInDistribution

/-- The identity map is a homeomorphism from `ProbabilityMeasure Ω` with the topology of
convergence in distribution to `ProbabilityMeasure Ω` with the Lévy-Prokhorov (pseudo)metric. -/
noncomputable def probabilityMeasureHomeomorph :
    ProbabilityMeasure Ω ≃ₜ LevyProkhorov (ProbabilityMeasure Ω) where
  toFun := LevyProkhorov.ofMeasure
  invFun := LevyProkhorov.toMeasure
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  continuous_invFun := LevyProkhorov.continuous_toMeasure_probabilityMeasure

@[deprecated (since := "2025-10-28")]
alias _root_.MeasureTheory.homeomorph_probabilityMeasure_levyProkhorov :=
  probabilityMeasureHomeomorph

end LevyProkhorov

/-- The topology of convergence in distribution on a separable space is pseudo-metrizable. -/
instance (X : Type*) [TopologicalSpace X] [PseudoMetrizableSpace X] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] :
    PseudoMetrizableSpace (ProbabilityMeasure X) :=
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  (LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)).isInducing.pseudoMetrizableSpace

/-- The topology of convergence in distribution on a separable Borel space is metrizable. -/
instance instMetrizableSpaceProbabilityMeasure (X : Type*) [TopologicalSpace X]
    [PseudoMetrizableSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    MetrizableSpace (ProbabilityMeasure X) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact LevyProkhorov.probabilityMeasureHomeomorph.isEmbedding.metrizableSpace

end Levy_Prokhorov_metrizes_convergence_in_distribution

end MeasureTheory -- namespace
