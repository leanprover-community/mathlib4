/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Martingale.BorelCantelli
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic

/-!

# The second Borel-Cantelli lemma

This file contains the *second Borel-Cantelli lemma* which states that, given a sequence of
independent sets `(sₙ)` in a probability space, if `∑ n, μ sₙ = ∞`, then the limsup of `sₙ` has
measure 1. We employ a proof using Lévy's generalized Borel-Cantelli by choosing an appropriate
filtration.

## Main result

- `ProbabilityTheory.measure_limsup_eq_one`: the second Borel-Cantelli lemma.

**Note**: for the *first Borel-Cantelli lemma*, which holds in general measure spaces (not only
in probability spaces), see `MeasureTheory.measure_limsup_atTop_eq_zero`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open scoped ENNReal Topology
open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section BorelCantelli

variable {ι β : Type*} [LinearOrder ι] [mβ : MeasurableSpace β] [NormedAddCommGroup β]
  [BorelSpace β] {f : ι → Ω → β} {i j : ι} {s : ι → Set Ω}

theorem iIndepFun.indep_comap_natural_of_lt (hf : ∀ i, StronglyMeasurable (f i))
    (hfi : iIndepFun f μ) (hij : i < j) :
    Indep (MeasurableSpace.comap (f j) mβ) (Filtration.natural f hf i) μ := by
  suffices Indep (⨆ k ∈ ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k ∈ {k | k ≤ i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)

theorem iIndepFun.condExp_natural_ae_eq_of_lt [SecondCountableTopology β] [CompleteSpace β]
    [NormedSpace ℝ β] (hf : ∀ i, StronglyMeasurable (f i)) (hfi : iIndepFun f μ)
    (hij : i < j) : μ[f j | Filtration.natural f hf i] =ᵐ[μ] fun _ => μ[f j] := by
  have : IsProbabilityMeasure μ := hfi.isProbabilityMeasure
  exact condExp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)

theorem iIndepSet.condExp_indicator_filtrationOfSet_ae_eq (hsm : ∀ n, MeasurableSet (s n))
    (hs : iIndepSet s μ) (hij : i < j) :
    μ[(s j).indicator (fun _ => 1 : Ω → ℝ) | filtrationOfSet hsm i] =ᵐ[μ]
    fun _ => μ.real (s j) := by
  rw [Filtration.filtrationOfSet_eq_natural (β := fun _ ↦ ℝ) hsm]
  refine (iIndepFun.condExp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans ?_
  simp only [integral_indicator_const _ (hsm _), smul_eq_mul, mul_one]; rfl

open Filter

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
theorem measure_limsup_eq_one {s : ℕ → Set Ω} (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ)
    (hs' : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1 := by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this, measure_univ]
  have : ∀ᵐ ω ∂μ, ∀ n, (μ[(s (n + 1)).indicator (1 : Ω → ℝ) | filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condExp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  refine eq_true (?_ : Tendsto _ _ _)
  simp_rw [hω]
  have htends : Tendsto (fun n => ∑ k ∈ Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  refine tendsto_atTop_atTop_of_monotone' ?_ ?_
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [← sub_nonneg, Finset.sum_range_succ_sub_sum]
    exact ENNReal.toReal_nonneg
  · rintro ⟨B, hB⟩
    refine not_eventually.2 (Frequently.of_forall fun n => ?_) (htends B.toNNReal)
    rw [mem_upperBounds] at hB
    specialize hB (∑ k ∈ Finset.range n, μ (s (k + 1))).toReal _
    · refine ⟨n, ?_⟩
      rw [ENNReal.toReal_sum (by finiteness)]
      rfl
    · rwa [not_lt, ENNReal.ofNNReal_toNNReal, ENNReal.le_ofReal_iff_toReal_le]
      · simp
      · exact le_trans (by positivity) hB

end BorelCantelli

end ProbabilityTheory
