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

section EquivalentConditions

/-! ### Portmanteau: the standard phrasings of the equivalent conditions

To facilitate organization, this section gives a few standard phrasings of the various conditions
whose equivalence is the statement of the portmanteau theorem.

We fix a space `Ω` with a topology (later assumed to be pseudo-metrizable) and a sigma-algebra
(later assumed to be at least as fine as the Borel sigma-algebra). We also fix an indexing
type `ι` and a filter `L` on it (later assumed to be countably-generated and nontrivial), and
a collection `Ps` of probability measures indexed by `ι` and a candidate limit probability
measure `P` on `Ω`. For formalization purposes, it is convenient to occasionally consider the
probability measures coerced to measures, so we also denote by `μs` a collection of measures
indexed by `ι` and by `μ` a measure on `Ω`.

Informally, the conditions are:

  (L) The probability measures `Ps` converge weakly (i.e., in distribution) to `P`.

  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` under the `Ps` is at most
      its measure under `P`.

  (O) For any open set `G` in `Ω` the liminf of the measures of `G` under the `Ps` is at least
      its measure under `P`.

  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries zero measure under `P`, the limit
      of the measures of `E` under the `Ps` equals its measure under `P`.

Variants of formal phrasings of these conditions are:
-/

variable {Ω ι : Type _} [TopologicalSpace Ω] [MeasurableSpace Ω] (L : Filter ι)
variable (μ : Measure Ω) (μs : ι → Measure Ω)
variable (P : ProbabilityMeasure Ω) (Ps : ι → ProbabilityMeasure Ω)

namespace Portmanteau

/-- The portmanteau condition (C): For any closed set `F`, the limsup of the measures of `F`
under the `Ps` is at most its measure under `P`. -/
private abbrev limsup_closed_le : Prop :=
  ∀ (F : Set Ω), IsClosed F → L.limsup (fun i ↦ Ps i F) ≤ P F

/-- The portmanteau condition (C'): For any closed set `F`, the limsup of the measures of `F`
under the `μs` is at most its measure under `μ`. (This is meant to be applied to the coerctions
of the probability measures to measures, the limsup is taken in `ℝ≥0∞`.) -/
private abbrev limsup_closed_le' : Prop :=
  ∀ (F : Set Ω), IsClosed F → L.limsup (fun i ↦ μs i F) ≤ μ F

/-- The portmanteau condition (O): For any open set `G`, the liminf of the measures of `G`
under the `Ps` is at least its measure under `P`. -/
private abbrev le_liminf_open : Prop :=
  ∀ (G : Set Ω), IsOpen G → P G ≤ L.liminf (fun i ↦ Ps i G)

/-- The portmanteau condition (O'): For any open set `G`, the liminf of the measures of `G`
under the `μs` is at least its measure under `μ`. (This is meant to be applied to the coerctions
of the probability measures to measures, the liminf is taken in `ℝ≥0∞`.) -/
private abbrev le_liminf_open' : Prop :=
  ∀ (G : Set Ω), IsOpen G → μ G ≤ L.liminf (fun i ↦ μs i G)

/-- The portmanteau condition (B): For any Borel set `E` whose boundary `∂E` carries zero measure
under `P`, the limit of the measures of `E` under the `Ps` equals its measure under `P`. -/
private abbrev tendsto_measure_of_null_frontier : Prop :=
  ∀ (E : Set Ω), MeasurableSet E → P (frontier E) = 0 → Tendsto (fun i ↦ Ps i E) L (𝓝 (P E))

/-- The portmanteau condition (B'): For any Borel set `E` whose boundary `∂E` carries zero measure
under `μ`, the limit of the measures of `E` under the `μs` equals its measure under `μ`. (This is
meant to be applied to the coerctions of the probability measures to measures, the limit is taken
in `ℝ≥0∞`.) -/
private abbrev tendsto_measure_of_null_frontier' : Prop :=
  ∀ (E : Set Ω), MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E))

variable [OpensMeasurableSpace Ω]

/-- The portmanteau condition (L): The probability measures `Ps` converge weakly
(i.e., in distribution) to `P`. -/
private abbrev tendsto_in_distribution := Tendsto Ps L (𝓝 P)

lemma tendsto_probability_iff_tendsto_measure (E : Set Ω) :
    Tendsto (fun i ↦ Ps i E) L (𝓝 (P E)) ↔
      Tendsto (fun i ↦ (Ps i : Measure Ω) E) L (𝓝 ((P : Measure Ω) E)) := by
  constructor <;> intro h
  · convert (ENNReal.continuous_coe.tendsto _).comp h <;> simp
  · convert (ENNReal.tendsto_toNNReal (show (P : Measure Ω) E ≠ ∞ from measure_ne_top P E)).comp h

lemma limsup_probability_le_iff_limsup_measure_le [NeBot L] (F : Set Ω) :
    L.limsup (fun i ↦ Ps i F) ≤ P F ↔
      L.limsup (fun i ↦ (Ps i : Measure Ω) F) ≤ (P : Measure Ω) F := by
  constructor <;> intro h
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε ε_pos PF_lt_top
    refine @limsup_le_of_le ℝ≥0∞ ι _ L (fun i ↦ (Ps i : Measure Ω) F) ((P : Measure Ω) F + ε) ?_ ?_
    · exact isBounded_ge_of_bot.isCobounded_le
    · have aux : P F < P F + ε := by simp [ε_pos]
      --have := lt_of_le_of_lt h aux
      have h' : L.limsup (fun i ↦ Ps i F) < P F + ε := lt_of_le_of_lt h aux
      --filter_upwards [eventually_lt_of_limsup_lt h'] with i hi
      have := @eventually_lt_of_limsup_lt ι ℝ≥0 L _ (fun i ↦ Ps i F) (P F + ε) h' ?_
      swap
      · simp only
        use 1
        simp only [eventually_map]
        apply eventually_of_forall
        intro i
        have : (Ps i F) ≤ 1 := by sorry -- :facepalm:
        exact this
      filter_upwards [this] with i hi
      simpa only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_add]
        using (@ENNReal.coe_le_coe (Ps i F) (P F + ε)).mpr hi.le
  · apply _root_.le_of_forall_pos_le_add
    intro ε ε_pos
    refine @limsup_le_of_le ℝ≥0 ι _ L (fun i ↦ Ps i F) (P F + ε) ?_ ?_
    · exact isBounded_ge_of_bot.isCobounded_le
    · have aux : (P : Measure Ω) F < (P : Measure Ω) F + ε := by
        convert (@ENNReal.add_lt_add_iff_left _ 0 ε _).mpr (by simp [ε_pos])
        · simp only [add_zero]
        · exact measure_ne_top P F
      filter_upwards [eventually_lt_of_limsup_lt (lt_of_le_of_lt h aux)] with i hi
      apply (@ENNReal.toNNReal_le_toNNReal (Ps i F) (P F + ε) ?_ ?_).mpr (by simp [hi.le]) <;>
      simp [measure_ne_top]

lemma le_liminf_probability_iff_le_liminf_measure (G : Set Ω) :
    P G ≤ L.liminf (fun i ↦ Ps i G) ↔
      (P : Measure Ω) G ≤ L.liminf (fun i ↦ (Ps i : Measure Ω) G) := by
  constructor <;> intro h
  · sorry
  · apply _root_.le_of_forall_pos_le_add
    intro ε ε_pos
    refine @limsup_le_of_le ℝ≥0 ι _ L (fun i ↦ μs i F) (μ F + ε) ?_ ?_
    · exact isBounded_ge_of_bot.isCobounded_le
    · have aux : (μ : Measure α) F < (μ : Measure α) F + ε := by
        convert (@ENNReal.add_lt_add_iff_left _ 0 ε _).mpr (by simp [ε_pos])
        · simp only [add_zero]
        · exact measure_ne_top μ F
      filter_upwards [eventually_lt_of_limsup_lt (lt_of_le_of_lt key aux)] with i hi
      apply (@ENNReal.toNNReal_le_toNNReal (μs i F) (μ F + ε) ?_ ?_).mpr (by simp [hi.le]) <;>
      simp [measure_ne_top]
    sorry

--lemma le_liminf_open_iff_le_liminf_open' {G : Set Ω} :
--  le_liminf_open

end Portmanteau

end EquivalentConditions

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

variable {Ω : Type _} [MeasurableSpace Ω]

theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type _} {L : Filter ι} {μ : Measure Ω}
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
    (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  have := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  exact antitone_const_tsub h
#align measure_theory.le_measure_compl_liminf_of_limsup_measure_le MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le

theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i Eᶜ) ≤ μ Eᶜ) :
    μ E ≤ L.liminf fun i => μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h
#align measure_theory.le_measure_liminf_of_limsup_measure_compl_le MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le

theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type _} {L : Filter ι} {μ : Measure Ω}
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
    (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  have := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simp_rw [← this]
  exact antitone_const_tsub h
#align measure_theory.limsup_measure_compl_le_of_le_liminf_measure MeasureTheory.limsup_measure_compl_le_of_le_liminf_measure

theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type _} {L : Filter ι} {μ : Measure Ω}
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
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type _} {L : Filter ι}
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
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`
implies that
  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries no mass under the candidate limit
      measure, we have that the limit of measures of `E` is the measure of `E` under the
      candidate limit measure.
-/


variable {Ω : Type _} [MeasurableSpace Ω]

theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type _} {L : Filter ι}
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
theorem tendsto_measure_of_null_frontier {ι : Type _} {L : Filter ι} {μ : Measure Ω}
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
pseudo-emetrizable, that the weak convergence of measures on `MeasureTheory.FiniteMeasure Ω`
implies that for any closed set `F` in `Ω` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.

Combining with an earlier implication we also get that weak convergence implies that for any Borel
set `E` in `Ω` whose boundary `∂E` carries no mass under the limit measure, the limit of measures
of `E` is the measure of `E` under the limit measure.
-/


variable {Ω : Type _} [MeasurableSpace Ω]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type _} {L : Filter ι}
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
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type _} [MeasurableSpace Ω]
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
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type _} {L : Filter ι}
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
    apply
      ENNReal.lt_add_right (lintegral_lt_top_of_boundedContinuous_to_nnreal (μ : Measure Ω) _).ne
        (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr ε_pos).ne.symm, ENNReal.two_ne_top⟩).ne.symm
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
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type _} {L : Filter ι}
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
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type _} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun _ F_closed => ProbabilityMeasure.limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))
#align measure_theory.probability_measure.le_liminf_measure_open_of_tendsto MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto

theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type _}
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
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type _} {L : Filter ι}
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

TODO: The proof of the implication is not yet here. Add it.
-/

open ENNReal

variable {Ω : Type _} [PseudoEMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem exists_null_frontier_thickening (μ : Measure Ω) [SigmaFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := @Measure.countable_meas_pos_of_disjoint_iUnion Ω _ _ μ _ _ mbles disjs
  have aux := @measure_diff_null ℝ _ volume (Ioo a b) _ (Set.Countable.measure_zero key volume)
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
Assuming that for all Borel sets `E` whose boundary `∂E` carries no probability mass under a
candidate limit probability measure `μ` we have convergence of the measures `μs i E` to `μ E`,
then for all closed sets `F` we have the limsup condition `limsup (μs i F) ≤ μ F`.

This is a version with coercions to ordinary `ℝ≥0∞`-valued measures. See
`MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_forall_tendsto_measure` for
a version with probability measures directly.
-/
lemma ProbabilityMeasure.limsup_measure_closed_le_of_forall_tendsto_measure'
    {α ι : Type _} {L : Filter ι} [NeBot L]
    [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α}
    (h : ∀ {E : Set α},
      MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set α) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ (μs i : Measure α) F) ≤ (μ : Measure α) F := by
  have h' : ∀ {E : Set α}, MeasurableSet E → (μ : Measure α) (frontier E) = 0 →
              Tendsto (fun i ↦ (μs i : Measure α) E) L (𝓝 ((μ : Measure α) E)) := by
    intro E E_mble E_nullbdry
    have obs := ENNReal.tendsto_coe.mpr (h E_mble (by simp only [E_nullbdry, zero_toNNReal]))
    simpa only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using obs
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : ∀ n, 0 < rs n := fun n ↦ ((Classical.choose_spec ex).2 n).1
  have rs_null : ∀ n, (μ : Measure α) (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n ↦ ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : ∀ n, IsOpen (Metric.thickening (rs n) F) :=
    fun n ↦ Metric.isOpen_thickening
  have key := fun (n : ℕ) ↦ h' (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intros ε ε_pos μF_finite
  have keyB := @tendsto_measure_cthickening_of_isClosed α _ _ _ μ F
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhd : Iio ((μ : Measure α) F + ε) ∈ 𝓝 ((μ : Measure α) F) := by
    apply Iio_mem_nhds
    simpa only [add_zero] using ENNReal.add_lt_add_left μF_finite.ne (ENNReal.coe_pos.mpr ε_pos)
  specialize rs_lim (keyB nhd)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux' := fun i ↦
    @measure_mono _ _ (μs i : Measure α) _ _ (Metric.self_subset_thickening (rs_pos m) F)
  have aux : (fun i ↦ ((μs i : Measure α) F))
              ≤ᶠ[L] (fun i ↦ (μs i : Measure α) (Metric.thickening (rs m) F)) := by
    exact eventually_of_forall aux'
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets `E` whose boundary `∂E` carries no probability mass under a
candidate limit probability measure `μ` we have convergence of the measures `μs i E` to `μ E`,
then for all closed sets `F` we have the limsup condition `limsup (μs i F) ≤ μ F`.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_forall_tendsto_measure'`.
-/
lemma ProbabilityMeasure.limsup_measure_closed_le_of_forall_tendsto_measure
    {α ι : Type _} {L : Filter ι} [NeBot L]
    [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α}
    (h : ∀ {E : Set α},
      MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set α) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ μs i F) ≤ μ F := by
  have key := limsup_measure_closed_le_of_forall_tendsto_measure' h F F_closed
  apply _root_.le_of_forall_pos_le_add
  intro ε ε_pos
  refine @limsup_le_of_le ℝ≥0 ι _ L (fun i ↦ μs i F) (μ F + ε) ?_ ?_
  · exact isBounded_ge_of_bot.isCobounded_le
  · have aux : (μ : Measure α) F < (μ : Measure α) F + ε := by
      convert (@ENNReal.add_lt_add_iff_left _ 0 ε _).mpr (by simp [ε_pos])
      · simp only [add_zero]
      · exact measure_ne_top μ F
    filter_upwards [eventually_lt_of_limsup_lt (lt_of_le_of_lt key aux)] with i hi
    apply (@ENNReal.toNNReal_le_toNNReal (μs i F) (μ F + ε) ?_ ?_).mpr (by simp [hi.le]) <;>
    simp [measure_ne_top]
/-
lemma ProbabilityMeasure.limsup_measure_closed_le_iff_tendsto_measure_of_null_frontier'
    {α ι : Type _} {L : Filter ι} [NeBot L]
    [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α} :
    (∀ {E : Set α}, MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
      ↔ (∀ {F : Set α}, IsClosed F → L.limsup (fun i ↦ μs i F) ≤ μ F) := by
  constructor <;> intro h
  · intro F F_closed
    exact limsup_measure_closed_le_of_forall_tendsto_measure h F F_closed
  · intro E E_mble E_nullbdry
    have aux := limsup_measure_closed_le_iff_liminf_measure_open_ge.mp h
    have := tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
 -/

lemma ProbabilityMeasure.limsup_measure_closed_le_iff_tendsto_measure_of_null_frontier
    {α ι : Type _} {L : Filter ι} [NeBot L]
    [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α} :
    (∀ {E : Set α}, MeasurableSet E → (μ : Measure α) (frontier E) = 0 →
        Tendsto (fun i ↦ (μs i : Measure α) E) L (𝓝 ((μ : Measure α) E)))
      ↔ (∀ {F : Set α}, IsClosed F → L.limsup (fun i ↦ (μs i : Measure α) F) ≤ (μ : Measure α) F) := by
  constructor <;> intro h
  · intro F F_closed
    apply limsup_measure_closed_le_of_forall_tendsto_measure'
    · intro E E_mble E_nullbdry
      have := h E_mble
      sorry
    · exact F_closed
  · intro E E_mble E_nullbdry
    have aux := limsup_measure_closed_le_iff_liminf_measure_open_ge.mp h
    have := tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
/-
    apply limsup_measure_closed_le_iff_tendsto_measure_of_null_frontier.mpr
    · intro F F_closed
      exact h F_closed
    · exact E_mble
    · exact E_nullbdry
 -/

end LimitBorelImpliesLimsupClosedLE --section

end MeasureTheory --namespace
