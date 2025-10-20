/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

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
* `MeasureTheory.tendsto_of_limsup_measure_closed_le` gives the implication (C) → (T).

We also deduce a practical convergence criterion for probability measures, in
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`.
Assume that, applied to all the elements of a π-system, a sequence of probability measures
converges to a limiting probability measure. Assume also that the π-system contains arbitrarily
small neighborhoods of any point. Then the sequence of probability measures converges for the
weak topology.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
more general assumptions than in the usual statement of portmanteau theorem. The full portmanteau
theorem, however, is most convenient for probability measures on pseudo-emetrizable spaces with
their Borel sigma algebras.

Some specific considerations on the assumptions in the different implications:
* `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`, i.e., implication (T) → (C),
  assumes that in the underlying topological space, indicator functions of closed sets have
  decreasing bounded continuous pointwise approximating sequences. The assumption is in the form
  of the type class `HasOuterApproxClosed`. Type class inference knows that for example the more
  common assumptions of metrizability or pseudo-emetrizability suffice.
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
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i E) ≤ μ E) :
    μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι ↦ 1 - μs i E) = L.liminf ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ) :
    μ E ≤ L.liminf fun i ↦ μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h

theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E ≤ L.liminf fun i ↦ μs i E) :
    (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι ↦ 1 - μs i E) = L.limsup ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ) :
    (L.limsup fun i ↦ μs i E) ≤ μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h

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
    (∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F) ↔
      ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G := by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))

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
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ ≤ L.liminf fun i ↦ μs i E₀)
    (h_E₁ : (L.limsup fun i ↦ μs i E₁) ≤ μ E₁) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ ≤ L.liminf fun i ↦ μs i E₀ := h_E₀
      _ ≤ L.liminf fun i ↦ μs i E :=
        liminf_le_liminf (.of_forall fun _ ↦ measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i ↦ μs i E) ≤ L.limsup fun i ↦ μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ ↦ measure_mono subset_E₁)
      _ ≤ μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
theorem tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)

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


/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n ↦ ∫⁻ ω, (fs n ω : ℝ≥0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a ↦ fs M a) <
      (lintegral (μ : Measure Ω) fun a ↦ fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n ↦ le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun _ F_closed ↦ limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))

theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
    fun _ G_open ↦ le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) := by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if a set is clopen, then the limit of the
measures of the set equals the measure of the set under the limit probability measure.
-/
theorem ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (hE : IsClopen E) : Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto μs_lim (by simp [hE])

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

section PseudoMetricSpace

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem exists_null_frontier_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r ↦ isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_diff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo, ← aux] at len_pos
  rcases nonempty_of_measure_ne_zero len_pos.ne.symm with ⟨r, ⟨r_in_Ioo, hr⟩⟩
  refine ⟨r, r_in_Ioo, ?_⟩
  simpa only [mem_setOf_eq, not_lt, le_zero_iff] using hr

theorem exists_null_frontiers_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) :
    ∃ rs : ℕ → ℝ,
      Tendsto rs atTop (𝓝 0) ∧ ∀ n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : ℝ) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : ℕ => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : ℕ => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n ↦ (obs n).choose_spec.1.1.le) fun n ↦ (obs n).choose_spec.1.2.le
  · exact fun n ↦ ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩

end PseudoMetricSpace

open TopologicalSpace

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all closed sets F we have the limsup condition limsup μsᵢ(F) ≤ μ(F). -/
lemma limsup_measure_closed_le_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι → Measure Ω}
    (h : ∀ {E : Set Ω}, MeasurableSet E → μ (frontier E) = 0 →
            Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set Ω) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ μs i F) ≤ μ F := by
  letI : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
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
  intro ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhds : Iio (μ F + ε) ∈ 𝓝 (μ F) :=
    Iio_mem_nhds <| ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhds)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i ↦ (μs i F)) ≤ᶠ[L] (fun i ↦ μs i (Metric.thickening (rs m) F)) :=
    .of_forall <| fun i ↦ measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all open sets G we have the limsup condition μ(G) ≤ liminf μsᵢ(G). -/
lemma le_liminf_measure_open_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
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

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) := ?_ -- (i)
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂(μs i)) := by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert ENNReal.toReal_mono ?_ same
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ nndist 0 g := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : ℝ≥0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp only [ge_iff_le, zero_le, forall_const])⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

theorem tendsto_of_forall_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ liminf (fun i ↦ (μs i : Measure Ω) G) atTop) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  refine tendsto_integral_of_forall_integral_le_liminf_integral fun f f_nn ↦ ?_
  exact integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure f_nn h_opens

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Superseded by `tendsto_of_forall_isOpen_le_liminf` which works for all countably
generated filters. -/
theorem tendsto_of_forall_isOpen_le_liminf_nat {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G G_open ↦ ?_
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i ↦ μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i ↦ μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert obs
  simp only [Function.comp_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothesis.
See `tendsto_of_forall_isOpen_le_liminf` for the version without coercion. -/
theorem tendsto_of_forall_isOpen_le_liminf' {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf (fun i ↦ (μs i : Measure Ω) G)) :
    L.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat' fun G hG ↦ ?_
  exact (h_opens G hG).trans (liminf_le_liminf_of_le hu)

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters. -/
theorem tendsto_of_forall_isOpen_le_liminf {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf (fun i ↦ μs i G)) :
    L.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat fun G hG ↦ (h_opens G hG).trans ?_
  change _ ≤ atTop.liminf ((fun i ↦ μs i G) ∘ u)
  rw [liminf_comp]
  refine liminf_le_liminf_of_le hu (by isBoundedDefault) ?_
  exact isBoundedUnder_of ⟨1, by simp⟩ |>.isCoboundedUnder_ge

end le_liminf_open_implies_convergence

section Closed

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    {L : Filter ι} [L.IsCountablyGenerated]

/-- One implication of the portmanteau theorem: if for all closed sets `F` we have the limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothesis.
See `tendsto_of_forall_isClosed_limsup_le` for the version without coercion. -/
lemma tendsto_of_forall_isClosed_limsup_le'
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ (μs i : Measure Ω) F) L ≤ (μ : Measure Ω) F) :
    Tendsto μs L (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]

lemma tendsto_of_forall_isClosed_limsup_le_nat {μs : ℕ → ProbabilityMeasure Ω}
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ μs i F) atTop ≤ μ F) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF_closed ↦ ?_
  specialize h F hF_closed
  have aux : ENNReal.ofNNReal (limsup (fun i ↦ μs i F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun i ↦ μs i F) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · F) (by fun_prop)
      ⟨1, by simp⟩ ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert obs
  simp

/-- One implication of the portmanteau theorem: if for all closed sets `F` we have the limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters. -/
theorem tendsto_of_forall_isClosed_limsup_le
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ μs i F) L ≤ μ F) :
    Tendsto μs L (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isClosed_limsup_le_nat fun F hF ↦ le_trans ?_ (h F hF)
  exact (limsup_comp (fun i ↦ μs i F) u _).trans_le
    (limsup_le_limsup_of_le hu (by isBoundedDefault) ⟨1, by simp⟩)

end Closed

section Lipschitz

variable {α ι E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f f' : ι → α → E} {g : α → E} {l : Filter ι}

lemma tendsto_integral_thickenedIndicator_of_isClosed {Ω : Type*}
    {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω}
    (s : Set Ω) (hs : IsClosed s)
    {δs : ℕ → ℝ} (δs_pos : ∀ (n : ℕ), 0 < δs n) (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
      ∫ ω, (thickenedIndicator (δs_pos n) s ω : ℝ) ∂μ)
      atTop (𝓝 ((μ : Measure Ω).real s)) := by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : ℕ → Ω → ℝ := fun n ω ↦ thickenedIndicator (δs_pos n) s ω
  have h_int n (ν : Measure Ω) [IsProbabilityMeasure ν] : Integrable (fs n) ν := by
    refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
    simp only [thickenedIndicator_apply, Real.norm_eq_abs, NNReal.abs_eq, NNReal.coe_le_one, fs]
    exact thickenedIndicator_le_one (δs_pos _) s x
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ hs δs_pos δs_lim
  have h_eq (n : ℕ) : ∫⁻ ω, thickenedIndicator (δs_pos n) s ω ∂μ
      = ENNReal.ofReal (∫ ω, fs n ω ∂μ) := by
    rw [lintegral_coe_eq_integral]
    exact h_int _ _
  simp_rw [h_eq] at h
  rw [Measure.real_def]
  have h_eq' : (fun n ↦ ∫ ω, fs n ω ∂μ) = fun n ↦ (ENNReal.ofReal (∫ ω, fs n ω ∂μ)).toReal := by
    ext n
    rw [ENNReal.toReal_ofReal]
    refine integral_nonneg fun x ↦ ?_
    simp [fs]
  rwa [h_eq', ENNReal.tendsto_toReal_iff (by simp) (by finiteness)]

/-- Weak convergence of probability measures is equivalent to the property that the integrals of
every bounded Lipschitz function converge to the integral of the function against
the limit measure. -/
theorem tendsto_iff_forall_lipschitz_integral_tendsto {γ Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {F : Filter γ} [F.IsCountablyGenerated]
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω → ℝ, (∃ (C : ℝ), ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  constructor
  · -- A bounded Lipschitz function is in particular a bounded continuous function, and we already
    -- know that weak convergence implies convergence of their integrals
    intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω ℝ :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using h f'
  -- To prove the other direction, we prove convergence of the measure of closed sets.
  -- We approximate the indicator function of a closed set by bounded Lipschitz functions.
  refine fun h ↦ tendsto_of_forall_isClosed_limsup_le' fun s hs ↦ ?_
  rcases F.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  suffices limsup (fun i ↦ (μs i : Measure Ω).real s) F ≤ (μ : Measure Ω).real s by
    simp only [Measure.real_def] at this
    rwa [ENNReal.limsup_toReal_eq (b := 1) (by simp) (.of_forall fun i ↦ prob_le_one),
      ENNReal.toReal_le_toReal _ (by finiteness)] at this
    refine ne_top_of_le_ne_top (b := 1) (by simp) ?_
    refine limsup_le_of_le ?_ (.of_forall fun i ↦ prob_le_one)
    exact isCoboundedUnder_le_of_le F (x := 0) (by simp)
  refine le_of_forall_pos_le_add fun ε ε_pos ↦ ?_
  let fs : ℕ → Ω → ℝ := fun n ω ↦ thickenedIndicator (δ := (1 : ℝ) / (n + 1)) (by positivity) s ω
  have h_int n (ν : Measure Ω) [IsProbabilityMeasure ν] : Integrable (fs n) ν := by
    refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
    simp only [one_div, Real.norm_eq_abs, NNReal.abs_eq, NNReal.coe_le_one, fs]
    exact thickenedIndicator_le_one _ s x
  have key₁ : Tendsto (fun n ↦ ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) :=
    tendsto_integral_thickenedIndicator_of_isClosed s hs (δs := fun n ↦ (1 : ℝ) / (n + 1))
      (fun _ ↦ by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ := h (fs M) ?_ ?_
  rotate_left
  · refine ⟨1, fun x y ↦ ?_⟩
    simp only [Real.dist_eq, abs_le]
    have h1 x : fs M x ≤ 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 ≤ fs M x := by simp [fs]
    grind
  · exact ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s⟩
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near : ∀ᶠ x in F, (μs x : Measure Ω).real s ≤ ∫ a, fs M a ∂μ + ε / 2 := by
    refine (key₂.eventually_le_const room₂).mono fun x hx ↦ le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ (h_int _ _) ?_
    · exact (integrable_indicator_iff hs.measurableSet).mpr (integrable_const _).integrableOn
    · have h : _ ≤ fs M :=
        (indicator_le_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s)
      simpa using h
  apply (Filter.limsup_le_limsup ev_near ?_ isBoundedUnder_const).trans
  · rw [limsup_const]
    apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
    ring
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)

end Lipschitz

section convergenceCriterion

open scoped Finset

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Given a π-system, if a sequence of measures converges along all elements of the π-system, then
it also converges along finite unions of elements of the π-system. -/
lemma _root_.IsPiSystem.tendsto_measureReal_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → Measure Ω} {ν : Measure Ω} {l : Filter ι}
    {t : Finset (Set Ω)} (ht : ∀ s ∈ t, s ∈ S)
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ s ∈ S, Tendsto (fun i ↦ (μ i).real s) l (𝓝 (ν.real s)))
    (hν : ∀ s ∈ S, ν s ≠ ∞ := by finiteness)
    (hμ : ∀ s ∈ S, ∀ i, μ i s ≠ ∞ := by finiteness) :
    Tendsto (fun i ↦ (μ i).real (⋃ s ∈ t, s)) l (𝓝 (ν.real (⋃ s ∈ t, s))) := by
  /- This statement is not completely obvious, as `⋃ s ∈ t, s` does not belong to the π-system `S`.
  However, thanks to the inclusion-exclusion formula one may express its measure in terms of
  measures of elements of `S`, from which the result follows. -/
  have A (i) : (μ i).real (⋃ s ∈ t, s) = ∑ u ∈ t.powerset with u.Nonempty,
      (-1 : ℝ) ^ (#u + 1) * (μ i).real (⋂ s ∈ u, s) :=
    measureReal_biUnion_eq_sum_powerset (fun s hs ↦ hmeas _ (ht _ hs))
      (fun s hs ↦ hμ _ (ht _ hs) i)
  simp_rw [A, measureReal_biUnion_eq_sum_powerset (fun s hs ↦ hmeas _ (ht _ hs))
    (fun s hs ↦ hν _ (ht _ hs))]
  refine tendsto_finset_sum _ (fun u hu ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hu
  apply Filter.Tendsto.const_mul
  rcases eq_empty_or_nonempty (⋂ s ∈ u, s) with h'u | h'u
  · simpa [h'u] using tendsto_const_nhds
  apply h
  exact hS.biInter_mem hu.2 (fun s hs ↦ ht _ (hu.1 hs)) h'u

/-- Given a π-system, if a sequence of probability measures converges along all elements of
the π-system, then it also converges along finite unions of elements of the π-system. -/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} {t : Finset (Set Ω)} (ht : ∀ s ∈ t, s ∈ S) (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ s ∈ S, Tendsto (fun i ↦ μ i s) l (𝓝 (ν s))) :
    Tendsto (fun i ↦ μ i (⋃ s ∈ t, s)) l (𝓝 (ν (⋃ s ∈ t, s))) := by
  have : Tendsto (fun i ↦ (μ i : Measure Ω).real (⋃ s ∈ t, s)) l
      (𝓝 ((ν : Measure Ω).real (⋃ s ∈ t, s))) := by
    apply hS.tendsto_measureReal_biUnion ht hmeas
    simpa using h
  simpa using this

/-- Consider a set of sets `S` containing arbitrarily small neighborhoods of any point, and a
probability measure. Then any open set can be approximated arbitrarily well in measure from inside
by a finite union of elements of `S`.

This is a technical lemma for `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`, which is
why it is formulated for a `ProbabilityMeasure`. If needed, this could be generalized to finite
measures or to general measures.
-/
lemma ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen
    [TopologicalSpace Ω] [SecondCountableTopology Ω]
    {S : Set (Set Ω)} (ν : ProbabilityMeasure Ω)
    (h : ∀ (u : Set Ω), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    {G : Set Ω} (hG : IsOpen G) {r : ℝ≥0} (hr : r < ν G) :
    ∃ T : Finset (Set Ω), (∀ t ∈ T, t ∈ S) ∧ (r < ν (⋃ t ∈ T, t)) ∧ (⋃ t ∈ T, t) ⊆ G := by
  classical
  obtain ⟨T, TS, T_count, hT⟩ : ∃ T : Set (Set Ω), T ⊆ S ∧ T.Countable ∧ ⋃ t ∈ T, t = G := by
    have : ∀ (x : G), ∃ s ∈ S, s ∈ 𝓝 (x : Ω) ∧ s ⊆ G := fun x ↦ h G hG x x.2
    choose! s hsS hs_nhds hsG using this
    rcases TopologicalSpace.isOpen_iUnion_countable (fun i ↦ interior (s i))
      (fun i ↦ isOpen_interior) with ⟨T₀, T₀_count, hT₀⟩
    refine ⟨s '' T₀, by grind, T₀_count.image s, ?_⟩
    refine Subset.antisymm (by simp; grind) ?_
    have : G ⊆ ⋃ i, interior (s i) := by
      intro y hy
      simpa using ⟨y, hy, mem_interior_iff_mem_nhds.2 (hs_nhds ⟨y, hy⟩)⟩
    apply this.trans
    rw [← hT₀, biUnion_image]
    exact iUnion₂_mono fun i j ↦ interior_subset
  have : T.Nonempty := by
    contrapose! hr
    simp [← hT, hr]
  rcases T_count.exists_eq_range this with ⟨f, hf⟩
  have G_eq : G = ⋃ n, f n := by simp [← hT, hf]
  have : Tendsto (fun i ↦ ν (Accumulate f i)) atTop (𝓝 (ν (⋃ i, f i))) :=
    (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
  rw [← G_eq] at this
  rcases ((tendsto_order.1 this).1 r hr).exists with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).image f, by grind, ?_, ?_⟩
  · convert hn
    simp [accumulate_def]
    grind
  · simpa [G_eq] using fun i _ ↦ subset_iUnion f i

/-- Assume that, applied to all the elements of a π-system, a sequence of probability measures
converges to a limiting probability measure. Assume also that the π-system contains arbitrarily
small neighborhoods of any point. Then the sequence of probability measures converges for the
weak topology. -/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    [TopologicalSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ (u : Set Ω), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (h' : ∀ s ∈ S, Tendsto (fun i ↦ μ i s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  /- We apply the portmanteau theorem: it suffices to show that, given an open set `G`
  and `r < ν G`, then for large `i` one has `r < μᵢ G`. For this, we approximate `G` from inside by
  a finite union `G'` of elements of `S`, still with measure `> r`, by Lemma
  `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`. If we have `μᵢ G' → ν G'`,
  then we deduce `r < μᵢ G'` for large `i`, and therefore `r < μᵢ G`.

  Our assumption does not give directly `μᵢ G' → ν G'`, as `G'` does not belong to the π-system `S`.
  However, the inclusion-exclusion formula makes it possible to express `μᵢ G'` and `ν G'` in terms
  of the measures of intersections of elements of `S`, for which we have the convergence. It follows
  that `μᵢ G' → ν G'` holds, concluding the proof. This second step is already formalized in the
  lemma `IsPiSystem.tendsto_probabilityMeasure_biUnion`. -/
  rcases l.eq_or_neBot with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) l (by simp)) (by isBoundedDefault)).2
    (fun r hr ↦ ?_)
  obtain ⟨T, TS, T_meas, TG⟩ :
      ∃ T : Finset (Set Ω), (∀ t ∈ T, t ∈ S) ∧ (r < ν (⋃ t ∈ T, t)) ∧ (⋃ t ∈ T, t) ⊆ G :=
    ν.exists_lt_measure_biUnion_of_isOpen h hG hr
  have : Tendsto (fun i ↦ μ i (⋃ t ∈ T, t)) l (𝓝 (ν (⋃ t ∈ T, t))) :=
    hS.tendsto_probabilityMeasure_biUnion TS hmeas h'
  filter_upwards [(tendsto_order.1 this).1 r T_meas] with i hi
  exact hi.trans_le <| ProbabilityMeasure.apply_mono _ TG

end convergenceCriterion

end MeasureTheory --namespace
