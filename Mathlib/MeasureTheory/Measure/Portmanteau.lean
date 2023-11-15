/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.Order.Bounded

#align_import measure_theory.measure.portmanteau from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Characterizations of weak convergence of finite measures and probability measures

This file will provide portmanteau characterizations of the weak convergence of finite measures
and of probability measures, i.e., the standard characterizations of convergence in distribution.

## Main definitions

The topologies of weak convergence on the types of finite measures and probability measures are
already defined in their corresponding files; no substantial new definitions are introduced here.

## Main results

The main result will be the portmanteau theorem providing various characterizations of the
weak convergence of measures (probability measures or finite measures). Given measures μs
and μ on a topological space Ω, the conditions that will be proven equivalent (under quite
general hypotheses) are:

  (T) The measures μs tend to the measure μ weakly.
  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).

The separate implications are:
 * `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto` is the implication (T) → (C).
 * `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` is the equivalence (C) ↔ (O).
 * `MeasureTheory.tendsto_measure_of_null_frontier` is the implication (O) → (B).
 * `MeasureTheory.limsup_measure_closed_le_of_forall_tendsto_measure` is the implication (B) → (C).
 * `MeasureTheory.tendsto_of_forall_isOpen_le_liminf` gives the implication (O) → (T) for
    any sequence of Borel probability measures.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
more general assumptions than in the usual statement of portmanteau theorem. The full portmanteau
theorem, however, is most convenient for probability measures on pseudo-emetrizable spaces with
their Borel sigma algebras.

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

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section LimsupClosedLEAndLELiminfOpen

/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i E) ≤ μ E) :
    μ Eᶜ ≤ L.liminf fun i => μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  have obs :
    (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E) := rfl
  rw [obs]
  have := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  exact antitone_const_tsub h
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
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  have obs :
    (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E) := rfl
  rw [obs]
  have := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  exact antitone_const_tsub h
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
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))
#align measure_theory.limsup_measure_closed_le_iff_liminf_measure_open_ge MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge

end LimsupClosedLEAndLELiminfOpen -- section

section TendstoOfNullFrontier

/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

implies that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
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
  · infer_param
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

end TendstoOfNullFrontier --section

section ConvergenceImpliesLimsupClosedLE

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (T) The measures μs tend to the measure μ weakly

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with a earlier proven implications, we get that (T) implies also both

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G);
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
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
  have aux : ∀ ω, indicator E (fun _ => (1 : ℝ≥0∞)) ω = ↑(indicator E (fun _ => (1 : ℝ≥0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
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
  rwa [F_closed.closure_eq] at key
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
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  let δs := fun n : ℕ => (1 : ℝ) / (n + 1)
  have δs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  have δs_lim : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_0_nat
  have key₁ :=
    tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure Ω) F_closed δs_pos δs_lim
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 := by
    apply
      ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne
        (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr ε_pos).ne.symm, ENNReal.two_ne_top⟩).ne.symm
  rcases eventually_atTop.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩
  have key₂ :=
    FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (thickenedIndicator (δs_pos M) F)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) <
      (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) + ε / 2 := by
    apply ENNReal.lt_add_right (ne_of_lt ?_)
        (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr ε_pos).ne.symm, ENNReal.two_ne_top⟩).ne.symm
    apply BoundedContinuousFunction.lintegral_lt_top_of_nnreal
  have ev_near := Eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) fun n => le_of_lt
  have ev_near' := Eventually.mono ev_near fun n => le_trans
    (measure_le_lintegral_thickenedIndicator (μs n : Measure Ω) F_closed.measurableSet (δs_pos M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]
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
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key
#align measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto

end ConvergenceImpliesLimsupClosedLE --section

section LimitBorelImpliesLimsupClosedLE

/-! ### Portmanteau implication: limit condition for Borel sets implies limsup for closed sets


In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B)

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with a earlier proven implications, we get that (B) implies also

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

-/

open ENNReal

variable {Ω : Type*} [PseudoEMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem exists_null_frontier_thickening (μ : Measure Ω) [SigmaFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_diff_null (s₁ := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo, ← aux] at len_pos
  rcases nonempty_of_measure_ne_zero len_pos.ne.symm with ⟨r, ⟨r_in_Ioo, hr⟩⟩
  refine' ⟨r, r_in_Ioo, _⟩
  simpa only [mem_setOf_eq, not_lt, le_zero_iff] using hr
#align measure_theory.exists_null_frontier_thickening MeasureTheory.exists_null_frontier_thickening

theorem exists_null_frontiers_thickening (μ : Measure Ω) [SigmaFinite μ] (s : Set Ω) :
    ∃ rs : ℕ → ℝ,
      Tendsto rs atTop (𝓝 0) ∧ ∀ n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : ℝ) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : ℕ => exists_null_frontier_thickening μ s (Rs_pos n)
  refine' ⟨fun n : ℕ => (obs n).choose, ⟨_, _⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n => (obs n).choose_spec.1.1.le) fun n => (obs n).choose_spec.1.2.le
  · exact fun n => ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩
#align measure_theory.exists_null_frontiers_thickening MeasureTheory.exists_null_frontiers_thickening

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all closed sets F we have the limsup condition limsup μsᵢ(F) ≤ μ(F). -/
lemma limsup_measure_closed_le_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [NeBot L]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι → Measure Ω}
    (h : ∀ {E : Set Ω}, MeasurableSet E → μ (frontier E) = 0 →
            Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set Ω) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ μs i F) ≤ μ F := by
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : ∀ n, 0 < rs n := fun n ↦ ((Classical.choose_spec ex).2 n).1
  have rs_null : ∀ n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n ↦ ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : ∀ n, IsOpen (Metric.thickening (rs n) F) :=
    fun n ↦ Metric.isOpen_thickening
  have key := fun (n : ℕ) ↦ h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intros ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhd : Iio (μ F + ε) ∈ 𝓝 (μ F) := by
    apply Iio_mem_nhds
    exact ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhd)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux' := fun i ↦ measure_mono (μ := μs i) (Metric.self_subset_thickening (rs_pos m) F)
  have aux : (fun i ↦ (μs i F)) ≤ᶠ[L] (fun i ↦ μs i (Metric.thickening (rs m) F)) :=
    eventually_of_forall aux'
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all open sets G we have the limsup condition μ(G) ≤ liminf μsᵢ(G). -/
lemma le_liminf_measure_open_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [NeBot L]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ {E}, MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (G : Set Ω) (G_open : IsOpen G) :
    μ G ≤ L.liminf (fun i ↦ μs i G) := by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)

end LimitBorelImpliesLimsupClosedLE --section

section le_liminf_open_implies_convergence

/-! ### Portmanteau implication: liminf condition for open sets implies weak convergence


In this section we prove for a sequence (μsₙ)ₙ Borel probability measures that

  (O) For any open set G, the liminf of the measures of G under μsₙ is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfₙ μsₙ(G).

implies

  (T) The measures μsₙ converge weakly to the measure μ.

-/

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall f_nn) f_cont.aemeasurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) := ?_ -- (i)
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (eventually_of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert (ENNReal.toReal_le_toReal ?_ ?_).mpr same
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (eventually_of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ nndist 0 g := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (eventually_of_forall bound)
  · exact (f.lintegral_of_real_lt_top μ).ne
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : ℝ≥0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, eventually_of_forall (by simp only [ge_iff_le, zero_le, forall_const])⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_to_continuous_fun] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

lemma tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  rcases eq_or_neBot L with rfl|hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_le_map_of_bounded_range _ obs
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_ge_map_of_bounded_range _ obs
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, (f x) ∂ (μs i)) (∫ x, (f x) ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

/-- One implication of the portmanteau theorem:
If for all open sets G we have the liminf condition `μ(G) ≤ liminf μsₙ(G)`, then the measures
μsₙ converge weakly to the measure μ. -/
theorem tendsto_of_forall_isOpen_le_liminf {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  apply tendsto_integral_of_forall_integral_le_liminf_integral
  intro f f_nn
  apply integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure (f := f) f_nn
  intro G G_open
  specialize h_opens G G_open
  simp only at h_opens
  have aux : ENNReal.ofNNReal (liminf (fun i ↦ ENNReal.toNNReal ((μs i : Measure Ω) G)) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i ↦ (ENNReal.toNNReal ((μs i : Measure Ω) G))) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · apply ENNReal.continuous_coe.continuousAt
    · use 1
      simp only [eventually_map, ProbabilityMeasure.apply_le_one, eventually_atTop, ge_iff_le,
        implies_true, forall_const, exists_const]
    · use 0
      simp only [zero_le, eventually_map, eventually_atTop, ge_iff_le, implies_true, forall_const,
        exists_const]
  have obs := ENNReal.coe_mono h_opens
  simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert obs
  simp only [Function.comp_apply, ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

end le_liminf_open_implies_convergence

end MeasureTheory --namespace
