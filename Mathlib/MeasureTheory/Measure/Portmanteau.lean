/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

#align_import measure_theory.measure.portmanteau from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Characterizations of weak convergence of finite measures and probability measures

This file will provide portmanteau characterizations of the weak convergence of finite measures
and of probability measures, i.e., the standard characterizations of convergence in distribution.

## Main definitions

This file does not introduce substantial new definitions: the topologies of weak convergence on
the types of finite measures and probability measures are already defined in their corresponding
files.

## Main results

The main result will be the portmanteau theorem providing various characterizations of the
weak convergence of measures. The separate implications are:
 * `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto` proves that weak convergence
   implies a limsup-condition for closed sets.
 * `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` proves for probability
   measures the equivalence of the limsup condition for closed sets and the liminf condition for
   open sets.
 * `MeasureTheory.tendsto_measure_of_null_frontier` proves that the liminf condition for open
   sets (which is equivalent to the limsup condition for closed sets) implies the convergence of
   probabilities of sets whose boundary carries no mass under the limit measure.
 * `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` is a
   combination of earlier implications, which shows that weak convergence of probability measures
   implies the convergence of probabilities of sets whose boundary carries no mass under the
   limit measure.

TODO:
 * Prove the rest of the implications.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
weaker assumptions than usually stated. The full portmanteau theorem, however, is most convenient
for probability measures on metrizable spaces with their Borel sigmas.

Some specific considerations on the assumptions in the different implications:
 * `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto` assumes
   `PseudoEMetricSpace`. The only reason is to have bounded continuous pointwise approximations
   to the indicator function of a closed set. Clearly for example metrizability or
   pseudo-emetrizability would be sufficient assumptions. The typeclass assumptions should be later
   adjusted in a way that takes into account use cases, but the proof will presumably remain
   essentially the same.
 * Where formulations are currently only provided for probability measures, one can obtain the
   finite measure formulations using the characterization of convergence of finite measures by
   their total masses and their probability-normalized versions, i.e., by
   `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, convergence in distribution, convergence in law, finite measure,
probability measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section LimsupClosedLEAndLELiminfOpen

/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`.
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`.
Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i E) ≤ μ E) :
    μ Eᶜ ≤ L.liminf fun i => μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  -- ⊢ ↑↑μ Eᶜ ≤ liminf (fun i => ↑↑(μs i) Eᶜ) ⊥
  · simp only [liminf_bot, le_top]
    -- 🎉 no goals
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  -- ⊢ 1 - ↑↑μ E ≤ liminf (fun i => 1 - ↑↑(μs i) E) L
  have obs :
    (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  -- ⊢ 1 - ↑↑μ E ≤ liminf ((fun x => 1 - x) ∘ fun i => ↑↑(μs i) E) L
  have := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  -- ⊢ 1 - ↑↑μ E ≤ 1 - limsup (fun i => ↑↑(μs i) E) L
  exact antitone_const_tsub h
  -- 🎉 no goals
#align measure_theory.le_measure_compl_liminf_of_limsup_measure_le MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le

theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i Eᶜ) ≤ μ Eᶜ) :
    μ E ≤ L.liminf fun i => μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h
#align measure_theory.le_measure_liminf_of_limsup_measure_compl_le MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le

theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E ≤ L.liminf fun i => μs i E) :
    (L.limsup fun i => μs i Eᶜ) ≤ μ Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  -- ⊢ limsup (fun i => ↑↑(μs i) Eᶜ) ⊥ ≤ ↑↑μ Eᶜ
  · simp only [limsup_bot, bot_le]
    -- 🎉 no goals
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  -- ⊢ limsup (fun i => 1 - ↑↑(μs i) E) L ≤ 1 - ↑↑μ E
  have obs :
    (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  -- ⊢ limsup ((fun x => 1 - x) ∘ fun i => ↑↑(μs i) E) L ≤ 1 - ↑↑μ E
  have := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  -- ⊢ 1 - liminf (fun i => ↑↑(μs i) E) L ≤ 1 - ↑↑μ E
  exact antitone_const_tsub h
  -- 🎉 no goals
#align measure_theory.limsup_measure_compl_le_of_le_liminf_measure MeasureTheory.limsup_measure_compl_le_of_le_liminf_measure

theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ Eᶜ ≤ L.liminf fun i => μs i Eᶜ) :
    (L.limsup fun i => μs i E) ≤ μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h
#align measure_theory.limsup_measure_le_of_le_liminf_measure_compl MeasureTheory.limsup_measure_le_of_le_liminf_measure_compl

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the closed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the open set
under a candidate limit measure.
-/
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μs i)] :
    (∀ F, IsClosed F → (L.limsup fun i => μs i F) ≤ μ F) ↔
      ∀ G, IsOpen G → μ G ≤ L.liminf fun i => μs i G := by
  constructor
  -- ⊢ (∀ (F : Set Ω), IsClosed F → limsup (fun i => ↑↑(μs i) F) L ≤ ↑↑μ F) → ∀ (G  …
  · intro h G G_open
    -- ⊢ ↑↑μ G ≤ liminf (fun i => ↑↑(μs i) G) L
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    -- ⊢ limsup (fun i => ↑↑(μs i) F) L ≤ ↑↑μ F
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))
#align measure_theory.limsup_measure_closed_le_iff_liminf_measure_open_ge MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge

end LimsupClosedLEAndLELiminfOpen

-- section
section TendstoOfNullFrontier

/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`
implies that
  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries no mass under the candidate limit
      measure, we have that the limit of measures of `E` is the measure of `E` under the
      candidate limit measure.
-/


variable {Ω : Type*} [MeasurableSpace Ω]

theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁)
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ ≤ L.liminf fun i => μs i E₀)
    (h_E₁ : (L.limsup fun i => μs i E₁) ≤ μ E₁) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ ≤ L.liminf fun i => μs i E₀ := h_E₀
      _ ≤ L.liminf fun i => μs i E :=
        liminf_le_liminf (eventually_of_forall fun _ => measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i => μs i E) ≤ L.limsup fun i => μs i E₁ :=
        limsup_le_limsup (eventually_of_forall fun _ => measure_mono subset_E₁)
      _ ≤ μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
    -- 🎉 no goals
  · infer_param
    -- 🎉 no goals
#align measure_theory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
theorem tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf fun i => μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i => μs i F) ≤ μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)
#align measure_theory.tendsto_measure_of_null_frontier MeasureTheory.tendsto_measure_of_null_frontier

end TendstoOfNullFrontier

--section
section ConvergenceImpliesLimsupClosedLE

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that the weak convergence of measures on `MeasureTheory.FiniteMeasure Ω`
implies that for any closed set `F` in `Ω` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.

Combining with an earlier implication we also get that weak convergence implies that for any Borel
set `E` in `Ω` whose boundary `∂E` carries no mass under the limit measure, the limit of measures
of `E` is the measure of `E` under the limit measure.
-/


variable {Ω : Type*} [MeasurableSpace Ω]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι → Ω →ᵇ ℝ≥0)
    (fs_bdd : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c)
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i : ι => ((⇑) : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs i) ω) L
      (𝓝 (indicator E (fun _ => (1 : ℝ≥0)) ω))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) L (𝓝 (μ E)) := by
  convert FiniteMeasure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  -- ⊢ ↑↑μ E = ∫⁻ (ω : Ω), ↑(indicator E (fun x => 1) ω) ∂μ
  have aux : ∀ ω, indicator E (fun _ => (1 : ℝ≥0∞)) ω = ↑(indicator E (fun _ => (1 : ℝ≥0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  -- ⊢ ↑↑μ E = ∫⁻ (x : Ω) in E, 1 ∂μ
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  -- 🎉 no goals
#align measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : ℕ → Ω →ᵇ ℝ≥0) (fs_bdd : ∀ n ω, fs n ω ≤ c)
    (fs_lim : Tendsto (fun n : ℕ => ((⇑) : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs n)) atTop
      (𝓝 (indicator E fun _ => (1 : ℝ≥0)))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    ∀ ω, Tendsto (fun n : ℕ => (fs n ω : ℝ≥0)) atTop (𝓝 (indicator E (fun _ => (1 : ℝ≥0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (eventually_of_forall fun n => eventually_of_forall (fs_bdd n)) (eventually_of_forall fs_lim')
#align measure_theory.measure_of_cont_bdd_of_tendsto_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral μ fun ω => (thickenedIndicator (δs_pos n) F ω : ℝ≥0∞)) atTop
      (𝓝 (μ F)) := by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n => thickenedIndicator (δs_pos n) F) fun n ω => thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  -- ⊢ Tendsto (fun n => ↑(thickenedIndicator (_ : 0 < δs n) F)) atTop (𝓝 (indicato …
  rwa [F_closed.closure_eq] at key
  -- 🎉 no goals
#align measure_theory.tendsto_lintegral_thickened_indicator_of_is_closed MeasureTheory.tendsto_lintegral_thickenedIndicator_of_isClosed

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  rcases L.eq_or_neBot with rfl | hne
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) ⊥ ≤ ↑↑↑μ F
  · simp only [limsup_bot, bot_le]
    -- 🎉 no goals
  apply ENNReal.le_of_forall_pos_le_add
  -- ⊢ ∀ (ε : ℝ≥0), 0 < ε → ↑↑↑μ F < ⊤ → limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + …
  intro ε ε_pos _
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  let δs := fun n : ℕ => (1 : ℝ) / (n + 1)
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  have δs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  have δs_lim : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_0_nat
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  have key₁ :=
    tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure Ω) F_closed δs_pos δs_lim
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 := by
    apply
      ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne
        (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr ε_pos).ne.symm, ENNReal.two_ne_top⟩).ne.symm
  rcases eventually_atTop.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  have key₂ :=
    FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (thickenedIndicator (δs_pos M) F)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) <
      (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) + ε / 2 := by
    apply
      ENNReal.lt_add_right (lintegral_lt_top_of_boundedContinuous_to_nnreal (μ : Measure Ω) _).ne
        (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr ε_pos).ne.symm, ENNReal.two_ne_top⟩).ne.symm
  have ev_near := Eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) fun n => le_of_lt
  -- ⊢ limsup (fun i => ↑↑↑(μs i) F) L ≤ ↑↑↑μ F + ↑ε
  have ev_near' := Eventually.mono ev_near fun n => le_trans
    (measure_le_lintegral_thickenedIndicator (μs n : Measure Ω) F_closed.measurableSet (δs_pos M))
  apply (Filter.limsup_le_limsup ev_near').trans
  -- ⊢ limsup (fun x => ∫⁻ (a : Ω), ↑(↑(thickenedIndicator (_ : 0 < δs M) F) a) ∂↑μ …
  rw [limsup_const]
  -- ⊢ ∫⁻ (a : Ω), ↑(↑(thickenedIndicator (_ : 0 < δs M) F) a) ∂↑μ + ↑ε / 2 ≤ ↑↑↑μ  …
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  -- ⊢ ↑↑↑μ F + ↑ε / 2 + ↑ε / 2 ≤ ↑↑↑μ F + ↑ε
  simp only [add_assoc, ENNReal.add_halves, le_refl]
  -- 🎉 no goals
#align measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω}
    (F_closed : IsClosed F) : (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed
#align measure_theory.probability_measure.limsup_measure_closed_le_of_tendsto MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun _ F_closed => ProbabilityMeasure.limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))
#align measure_theory.probability_measure.le_liminf_measure_open_of_tendsto MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto

theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G :=
    fun _ G_open => ProbabilityMeasure.le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry
#align measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto' MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i => μs i E) L (𝓝 (μ E)) := by
  have E_nullbdry' : (μ : Measure Ω) (frontier E) = 0 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, E_nullbdry, ENNReal.coe_zero]
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' μs_lim E_nullbdry'
  -- ⊢ Tendsto (fun i => (fun s => ENNReal.toNNReal (↑↑↑(μs i) s)) E) L (𝓝 ((fun s  …
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key
  -- 🎉 no goals
#align measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto

end ConvergenceImpliesLimsupClosedLE

--section
section LimitBorelImpliesLimsupClosedLE

/-! ### Portmanteau implication: limit condition for Borel sets implies limsup for closed sets

TODO: The proof of the implication is not yet here. Add it.
-/


variable {Ω : Type*} [PseudoEMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem exists_null_frontier_thickening (μ : Measure Ω) [SigmaFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  have key := @Measure.countable_meas_pos_of_disjoint_iUnion Ω _ _ μ _ _ mbles disjs
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  have aux := @measure_diff_null ℝ _ volume (Ioo a b) _ (Set.Countable.measure_zero key volume)
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  rw [← Real.volume_Ioo, ← aux] at len_pos
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  rcases nonempty_of_measure_ne_zero len_pos.ne.symm with ⟨r, ⟨r_in_Ioo, hr⟩⟩
  -- ⊢ ∃ r, r ∈ Ioo a b ∧ ↑↑μ (frontier (Metric.thickening r s)) = 0
  refine' ⟨r, r_in_Ioo, _⟩
  -- ⊢ ↑↑μ (frontier (Metric.thickening r s)) = 0
  simpa only [mem_setOf_eq, not_lt, le_zero_iff] using hr
  -- 🎉 no goals
#align measure_theory.exists_null_frontier_thickening MeasureTheory.exists_null_frontier_thickening

theorem exists_null_frontiers_thickening (μ : Measure Ω) [SigmaFinite μ] (s : Set Ω) :
    ∃ rs : ℕ → ℝ,
      Tendsto rs atTop (𝓝 0) ∧ ∀ n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : ℝ) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  -- ⊢ ∃ rs, Tendsto rs atTop (𝓝 0) ∧ ∀ (n : ℕ), 0 < rs n ∧ ↑↑μ (frontier (Metric.t …
  have obs := fun n : ℕ => exists_null_frontier_thickening μ s (Rs_pos n)
  -- ⊢ ∃ rs, Tendsto rs atTop (𝓝 0) ∧ ∀ (n : ℕ), 0 < rs n ∧ ↑↑μ (frontier (Metric.t …
  refine' ⟨fun n : ℕ => (obs n).choose, ⟨_, _⟩⟩
  -- ⊢ Tendsto (fun n => Exists.choose (_ : ∃ r, r ∈ Ioo 0 (Rs n) ∧ ↑↑μ (frontier ( …
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n => (obs n).choose_spec.1.1.le) fun n => (obs n).choose_spec.1.2.le
  · exact fun n => ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩
    -- 🎉 no goals
#align measure_theory.exists_null_frontiers_thickening MeasureTheory.exists_null_frontiers_thickening

end LimitBorelImpliesLimsupClosedLE

--section
end MeasureTheory

--namespace
