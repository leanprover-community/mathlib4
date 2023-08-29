/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic

#align_import probability.borel_cantelli from "leanprover-community/mathlib"@"2f8347015b12b0864dfaf366ec4909eb70c78740"

/-!

# The second Borel-Cantelli lemma

This file contains the second Borel-Cantelli lemma which states that, given a sequence of
independent sets `(sₙ)` in a probability space, if `∑ n, μ sₙ = ∞`, then the limsup of `sₙ` has
measure 1. We employ a proof using Lévy's generalized Borel-Cantelli by choosing an appropriate
filtration.

## Main result

- `ProbabilityTheory.measure_limsup_eq_one`: the second Borel-Cantelli lemma.

-/


open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators Topology

open MeasureTheory ProbabilityTheory MeasurableSpace TopologicalSpace

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

section BorelCantelli

variable {ι β : Type*} [LinearOrder ι] [mβ : MeasurableSpace β] [NormedAddCommGroup β]
  [BorelSpace β] {f : ι → Ω → β} {i j : ι} {s : ι → Set Ω}

theorem iIndepFun.indep_comap_natural_of_lt (hf : ∀ i, StronglyMeasurable (f i))
    (hfi : iIndepFun (fun _ => mβ) f μ) (hij : i < j) :
    Indep (MeasurableSpace.comap (f j) mβ) (Filtration.natural f hf i) μ := by
  suffices Indep (⨆ k ∈ ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k ∈ {k | k ≤ i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.indep_comap_natural_of_lt ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt

theorem iIndepFun.condexp_natural_ae_eq_of_lt [SecondCountableTopology β] [CompleteSpace β]
    [NormedSpace ℝ β] (hf : ∀ i, StronglyMeasurable (f i)) (hfi : iIndepFun (fun _ => mβ) f μ)
    (hij : i < j) : μ[f j|Filtration.natural f hf i] =ᵐ[μ] fun _ => μ[f j] :=
  condexp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.condexp_natural_ae_eq_of_lt ProbabilityTheory.iIndepFun.condexp_natural_ae_eq_of_lt

theorem iIndepSet.condexp_indicator_filtrationOfSet_ae_eq (hsm : ∀ n, MeasurableSet (s n))
    (hs : iIndepSet s μ) (hij : i < j) :
    μ[(s j).indicator (fun _ => 1 : Ω → ℝ)|filtrationOfSet hsm i] =ᵐ[μ]
    fun _ => (μ (s j)).toReal := by
  rw [Filtration.filtrationOfSet_eq_natural (β := ℝ) hsm]
  -- ⊢ μ[Set.indicator (s j) fun x => 1|↑(Filtration.natural (fun i => Set.indicato …
  refine' (iIndepFun.condexp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans _
  -- ⊢ (fun x => ∫ (x : Ω), Set.indicator (s j) (fun _ω => 1) x ∂μ) =ᵐ[μ] fun x =>  …
  simp only [integral_indicator_const _ (hsm _), Algebra.id.smul_eq_mul, mul_one]; rfl
  -- ⊢ (fun x => ENNReal.toReal (↑↑μ (s j))) =ᵐ[μ] fun x => ENNReal.toReal (↑↑μ (s  …
                                                                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_set.condexp_indicator_filtration_of_set_ae_eq ProbabilityTheory.iIndepSet.condexp_indicator_filtrationOfSet_ae_eq

open Filter

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
theorem measure_limsup_eq_one {s : ℕ → Set Ω} (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ)
    (hs' : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1 := by
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k in Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this, measure_univ]
  have : ∀ᵐ ω ∂μ, ∀ n, (μ[(s (n + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condexp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  -- ⊢ setOf (fun ω => Tendsto (fun n => ∑ k in Finset.range n, (μ[Set.indicator (s …
  refine' eq_true (_ : Tendsto _ _ _)
  -- ⊢ Tendsto (fun n => ∑ k in Finset.range n, (μ[Set.indicator (s (k + 1)) 1|↑(fi …
  simp_rw [hω]
  -- ⊢ Tendsto (fun n => ∑ x in Finset.range n, ENNReal.toReal (↑↑μ (s (x + 1)))) a …
  have htends : Tendsto (fun n => ∑ k in Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  -- ⊢ Tendsto (fun n => ∑ x in Finset.range n, ENNReal.toReal (↑↑μ (s (x + 1)))) a …
  refine' tendsto_atTop_atTop_of_monotone' _ _
  -- ⊢ Monotone fun n => ∑ x in Finset.range n, ENNReal.toReal (↑↑μ (s (x + 1)))
  · refine' monotone_nat_of_le_succ fun n => _
    -- ⊢ ∑ x in Finset.range n, ENNReal.toReal (↑↑μ (s (x + 1))) ≤ ∑ x in Finset.rang …
    rw [← sub_nonneg, Finset.sum_range_succ_sub_sum]
    -- ⊢ 0 ≤ ENNReal.toReal (↑↑μ (s (n + 1)))
    exact ENNReal.toReal_nonneg
    -- 🎉 no goals
  · rintro ⟨B, hB⟩
    -- ⊢ False
    refine' not_eventually.2 (frequently_of_forall fun n => _) (htends B.toNNReal)
    -- ⊢ ¬↑(Real.toNNReal B) < ∑ k in Finset.range n, ↑↑μ (s (k + 1))
    rw [mem_upperBounds] at hB
    -- ⊢ ¬↑(Real.toNNReal B) < ∑ k in Finset.range n, ↑↑μ (s (k + 1))
    specialize hB (∑ k : ℕ in Finset.range n, μ (s (k + 1))).toReal _
    -- ⊢ ENNReal.toReal (∑ k in Finset.range n, ↑↑μ (s (k + 1))) ∈ Set.range fun n => …
    · refine' ⟨n, _⟩
      -- ⊢ (fun n => ∑ x in Finset.range n, ENNReal.toReal (↑↑μ (s (x + 1)))) n = ENNRe …
      rw [ENNReal.toReal_sum]
      -- ⊢ ∀ (a : ℕ), a ∈ Finset.range n → ↑↑μ (s (a + 1)) ≠ ⊤
      exact fun _ _ => measure_ne_top _ _
      -- 🎉 no goals
    · rw [not_lt, ← ENNReal.toReal_le_toReal (ENNReal.sum_lt_top _).ne ENNReal.coe_ne_top]
      -- ⊢ ENNReal.toReal (∑ a in Finset.range n, ↑↑μ (s (a + 1))) ≤ ENNReal.toReal ↑(R …
      · exact hB.trans (by simp)
        -- 🎉 no goals
      · exact fun _ _ => measure_ne_top _ _
        -- 🎉 no goals
#align probability_theory.measure_limsup_eq_one ProbabilityTheory.measure_limsup_eq_one

end BorelCantelli

end ProbabilityTheory
