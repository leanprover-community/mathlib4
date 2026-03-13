import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.Ring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Martingale.Kolmogorov
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance

open scoped BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace Kolmogorov

section Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ae_exists_tendsto_tailPartialSum_of_summable_variance_of_mean_zero
    (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i))
    (hXL2 : ∀ i, MemLp (X i) 2 μ)
    (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X (i + 1)] = 0)
    (hVar : Summable (fun i => variance (X (i + 1)) μ)) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ,
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, X (i + 1) ω) Filter.atTop (nhds c) := by
  let ℱ := Filtration.natural X hXm
  let S : ℕ → Ω → ℝ := fun n => ∑ i ∈ Finset.range n, X (i + 1)
  have hXadp : StronglyAdapted ℱ X := id (Filtration.stronglyAdapted_natural hXm)
  have hSadp : StronglyAdapted ℱ S := by
    intro n
    exact Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
      hXadp.stronglyMeasurable_le (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hSL2 : ∀ n, MemLp (S n) 2 μ := by
    intro n
    exact memLp_finset_sum' (s := Finset.range n) (fun k hk => hXL2 (k + 1))
  have hSint : ∀ n, Integrable (S n) μ := by
    intro n
    exact (hSL2 n).integrable (by norm_num)
  have hSmart : Martingale S ℱ μ := by
    exact martingale_of_condExp_sub_eq_zero_nat hSadp hSint (fun i => by
      calc
        μ[S (i + 1) - S i | ℱ i] =ᵐ[μ] μ[X (i + 1) | ℱ i] := by
          refine condExp_congr_ae ?_
          filter_upwards with ω
          simp [S, Finset.sum_range_succ_sub_sum]
        _ =ᵐ[μ] fun _ => μ[X (i + 1)] := by
          simpa [ℱ] using iIndepFun.condExp_natural_ae_eq_of_lt hXm hXind (i.lt_succ_self)
        _ =ᵐ[μ] 0 := by
          filter_upwards with ω
          simp [hXmean i])
  have hSsub : Submartingale S ℱ μ := hSmart.submartingale
  have hVarS_eq : ∀ n, variance (S n) μ = ∑ k ∈ Finset.range n, variance (X (k + 1)) μ := by
    intro n
    simpa [S] using (IndepFun.variance_sum
      (fun i hi => hXL2 (i + 1))
      (fun ⦃i⦄ hi ⦃j⦄ hj hij => hXind.indepFun (Function.Injective.ne Nat.succ_injective hij)))
  have hVarS_le : ∀ n, variance (S n) μ ≤ ∑' i, variance (X (i + 1)) μ := by
    intro n
    rw [hVarS_eq n]
    exact hVar.sum_le_tsum (Finset.range n) (fun i hi => variance_nonneg _ _)
  have hSmean : ∀ n, μ[S n] = 0 := by
    intro n
    have hsum : ∫ x, (∑ k ∈ Finset.range n, X (k + 1) x) ∂μ = 0 := by
      rw [integral_finset_sum _ (fun k hk => (hXL2 (k + 1)).integrable (by norm_num))]
      exact Finset.sum_eq_zero fun k hk => hXmean k
    simpa [S] using hsum
  have hSL2_bound : ∀ n,
      eLpNorm (S n) 2 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ)) := by
    intro n
    have hLp2 : eLpNorm (S n) 2 μ = ENNReal.ofReal ((∫ ω, ‖S n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
      simpa using (MemLp.eLpNorm_eq_integral_rpow_norm
        (f := S n) two_ne_zero ENNReal.ofNat_ne_top (hSL2 n))
    have hnormpow : (∫ ω, ‖S n ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, (S n ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      simp [Real.norm_eq_abs, sq_abs]
    rw [hLp2, hnormpow, ← variance_of_integral_eq_zero (MemLp.aemeasurable (hSL2 n)) (hSmean n)]
    have hpow : (variance (S n) μ) ^ (1 / (2 : ℝ)) ≤ (∑' i, variance (X (i + 1)) μ) ^ (1 / (2 : ℝ)) :=
      Real.rpow_le_rpow (variance_nonneg (S n) μ) (hVarS_le n) (by positivity)
    simpa [Real.sqrt_eq_rpow] using ENNReal.ofReal_le_ofReal hpow
  have hbdd : ∃ R : NNReal, ∀ n, eLpNorm (S n) 1 μ ≤ R := by
    refine ⟨(ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ))).toNNReal, ?_⟩
    intro n
    have h12 : eLpNorm (S n) 1 μ ≤ eLpNorm (S n) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (show (1 : ENNReal) ≤ 2 by norm_num)
        (hSL2 n).aestronglyMeasurable
    have h2 : eLpNorm (S n) 2 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ)) :=
      hSL2_bound n
    have hbound : eLpNorm (S n) 1 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ)) :=
      h12.trans h2
    simpa [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top] using hbound
  rcases hbdd with ⟨R, hR⟩
  simpa [S] using (hSsub.exists_ae_tendsto_of_bdd hR)

lemma ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
    (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i))
    (hXL2 : ∀ i, MemLp (X i) 2 μ)
    (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X i] = 0)
    (hVar : Summable (fun i => variance (X i) μ)) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ,
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, X i ω) Filter.atTop (nhds c) := by
  have htail := ae_exists_tendsto_tailPartialSum_of_summable_variance_of_mean_zero
    (μ := μ) X hXm hXL2 hXind (fun i => hXmean (i + 1)) ((summable_nat_add_iff 1).2 hVar)
  filter_upwards [htail] with ω hω
  rcases hω with ⟨c, hc⟩
  refine ⟨X 0 ω + c, ?_⟩
  have hsucc :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), X i ω) Filter.atTop (nhds (X 0 ω + c)) := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) ((hc.const_add (X 0 ω)))
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_range_succ' (f := fun i => X i ω) n).symm
  exact (Filter.tendsto_add_atTop_iff_nat
    (f := fun n => ∑ i ∈ Finset.range n, X i ω) (l := nhds (X 0 ω + c)) 1).1 hsucc

/-- Kolmogorov's two-series theorem for real-valued random variables.
If the series of means and the series of variances converge, then partial sums converge a.s. -/
theorem kolmogorov_two_series
    (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i))
    (hXL2 : ∀ i, MemLp (X i) 2 μ)
    (hXind : iIndepFun X μ)
    (hMean : Summable (fun i => μ[X i]))
    (hVar : Summable (fun i => variance (X i) μ)) :
    ∀ᵐ ω ∂μ, ∃ x : ℝ,
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, X i ω) Filter.atTop (nhds x) := by
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω - μ[X i]
  have hYm : ∀ i, StronglyMeasurable (Y i) := by
    intro i
    exact (hXm i).sub stronglyMeasurable_const
  have hYL2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    exact (hXL2 i).sub (memLp_const (μ[X i]))
  have hYind : iIndepFun Y μ := by
    simpa [Y, Function.comp] using
      hXind.comp (fun i x => x - μ[X i]) (fun i => measurable_id.sub measurable_const)
  have hYmean : ∀ i, μ[Y i] = 0 := by
    intro i
    simp [Y]
    rw [integral_sub ((hXL2 i).integrable (by norm_num)) (integrable_const _)]
    simp [integral_const]
  have hYVar : Summable (fun i => variance (Y i) μ) := by
    refine hVar.congr ?_
    intro i
    simpa [Y] using (variance_sub_const (μ := μ) ((hXm i).aestronglyMeasurable) (μ[X i])).symm
  have hYconv := ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
    (μ := μ) Y hYm hYL2 hYind hYmean hYVar
  have hMeanConv :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, μ[X i]) Filter.atTop (nhds (∑' i, μ[X i])) :=
    hMean.hasSum.tendsto_sum_nat
  filter_upwards [hYconv] with ω hω
  rcases hω with ⟨c, hc⟩
  refine ⟨c + ∑' i, μ[X i], ?_⟩
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) (hc.add hMeanConv)
  simp [Y]

end Real

end Kolmogorov
