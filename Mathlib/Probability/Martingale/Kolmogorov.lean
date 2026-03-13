/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Probability.BorelCantelli

/-!
### Results

* `kolmogorov_ineq_wiki_version_of_iIndepFun`:

### References

* https://en.wikipedia.org/wiki/Kolmogorov%27s_inequality
* https://en.wikipedia.org/wiki/Kolmogorov%27s_two-series_theorem
-/

@[expose] public section


open MeasureTheory ProbabilityTheory Finset

section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → ℝ}

theorem kolmogorov_ineq_wiki_version_of_iIndepFun
    (hXm : ∀ i, StronglyMeasurable (X i)) (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X (i + 1)] = 0) (hXL2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) (ε : NNReal) :
    ε ^ 2 * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one
      (fun k => |∑ j ∈ range k, X (j + 1) ω|)}
    ≤ ENNReal.ofReal (∑ k ∈ range n, ∫ ω, (X (k + 1) ω) ^ 2 ∂μ) := by
  let ℱ : Filtration ℕ m0 := Filtration.natural X hXm
  let S : ℕ → Ω → ℝ := fun m => ∑ k ∈ range m, X (k + 1)
  have hXadp : StronglyAdapted ℱ X := id (Filtration.stronglyAdapted_natural hXm)
  have hSadp : StronglyAdapted ℱ S := fun m => (stronglyMeasurable_sum (range m) fun k hk =>
    hXadp.stronglyMeasurable_le (Nat.succ_le_of_lt (mem_range.mp hk)))
  have hSL2 : ∀ m, MemLp (S m) 2 μ := fun m =>
    id (memLp_finset_sum' (range m) fun k hk => hXL2 (k + 1))
  have hSint : ∀ m, Integrable (S m) μ := fun m => (hSL2 m).integrable (by norm_num)
  have hSmart : Martingale S ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hSadp hSint fun i => ?_
    calc
      _ =ᵐ[μ] μ[X (i + 1) | ℱ i] := condExp_congr_ae <| by simp [S, sum_range_succ_sub_sum]
      _ =ᵐ[μ] fun _ => μ[X (i + 1)] := id
        (iIndepFun.condExp_natural_ae_eq_of_lt hXm hXind (i.lt_succ_self))
      _ =ᵐ[μ] _ := Filter.univ_mem' (id fun ω ↦ id (hXmean i))
  calc
    _ ≤ ENNReal.ofReal (Var[S n; μ]) := by
      have hSmean : μ[S n] = 0 := by
        rw [show S n = ∑ k ∈ range n, X (k + 1) by rfl]
        simp only [Finset.sum_apply]
        rw [integral_finset_sum _ (fun k hk => (hXL2 (k + 1)).integrable (by norm_num))]
        exact sum_eq_zero fun k hk => hXmean k
      simpa [S] using kolmogorov_ineq_wiki_version hSmart hSL2 n ε hSmean
    _ = _ := by
      have hVarSum : Var[S n; μ] = ∑ k ∈ range n, Var[X (k + 1); μ] := id
        (IndepFun.variance_sum (fun i hi => hXL2 (i + 1)) fun ⦃i⦄ hi ⦃j⦄ hj hij =>
          iIndepFun.indepFun hXind (Function.Injective.ne Nat.succ_injective hij))
      have hVarSq : (∑ k ∈ range n, Var[X (k + 1); μ]) = ∑ k ∈ range n, ∫ ω, (X (k + 1) ω) ^ 2 ∂μ :=
        sum_congr rfl fun k hk =>
          variance_of_integral_eq_zero (MemLp.aemeasurable (hXL2 (k + 1))) (hXmean k)
      rw [hVarSum, hVarSq]

lemma ae_exists_tendsto_tailPartialSum_of_summable_variance_of_mean_zero
    (hXm : ∀ i, StronglyMeasurable (X i)) (hXL2 : ∀ i, MemLp (X i) 2 μ) (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X (i + 1)] = 0) (hVar : Summable (fun i => variance (X (i + 1)) μ)) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ,
      Filter.Tendsto (fun n => ∑ i ∈ range n, X (i + 1) ω) Filter.atTop (nhds c) := by
  let ℱ := Filtration.natural X hXm
  let S : ℕ → Ω → ℝ := fun n => ∑ i ∈ range n, X (i + 1)
  have hXadp : StronglyAdapted ℱ X := id (Filtration.stronglyAdapted_natural hXm)
  have hSadp : StronglyAdapted ℱ S := fun n ↦ stronglyMeasurable_sum (range n) fun k hk ↦
    StronglyAdapted.stronglyMeasurable_le hXadp (Nat.succ_le_of_lt (mem_range.mp hk))
  have hSL2 : ∀ n, MemLp (S n) 2 μ := fun n ↦ memLp_finset_sum' (range n) fun k hk ↦ hXL2 (k + 1)
  have hSint : ∀ n, Integrable (S n) μ := fun n ↦ (hSL2 n).integrable (by norm_num)
  have hSmart : Martingale S ℱ μ := by
    exact martingale_of_condExp_sub_eq_zero_nat hSadp hSint (fun i => by
      calc
        _ =ᵐ[μ] μ[X (i + 1) | ℱ i] := by
          refine condExp_congr_ae ?_
          simp [S, Finset.sum_range_succ_sub_sum]
        _ =ᵐ[μ] fun _ => μ[X (i + 1)] := by
          simpa [ℱ] using iIndepFun.condExp_natural_ae_eq_of_lt hXm hXind (i.lt_succ_self)
        _ =ᵐ[μ] _ := by
          filter_upwards with ω
          simp [hXmean i])
  have hSsub : Submartingale S ℱ μ := hSmart.submartingale
  have hVarS_eq : ∀ n, variance (S n) μ = ∑ k ∈ range n, variance (X (k + 1)) μ := by
    intro n
    simpa [S] using (IndepFun.variance_sum
      (fun i hi => hXL2 (i + 1))
      (fun _ hi _ hj hij => hXind.indepFun (Function.Injective.ne Nat.succ_injective hij)))
  have hVarS_le : ∀ n, variance (S n) μ ≤ ∑' i, variance (X (i + 1)) μ := by
    intro n
    rw [hVarS_eq n]
    exact hVar.sum_le_tsum (range n) (fun i hi => variance_nonneg _ _)
  have hSmean : ∀ n, μ[S n] = 0 := by
    intro n
    have hsum : ∫ x, (∑ k ∈ range n, X (k + 1) x) ∂μ = 0 := by
      rw [integral_finset_sum _ (fun k hk => (hXL2 (k + 1)).integrable (by norm_num))]
      exact Finset.sum_eq_zero fun k hk => hXmean k
    simpa [S] using hsum
  have hSL2_bound : ∀ n,
      eLpNorm (S n) 2 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ)) := by
    intro n
    have hLp2 : eLpNorm (S n) 2 μ
        = ENNReal.ofReal ((∫ ω, ‖S n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
      simpa using (MemLp.eLpNorm_eq_integral_rpow_norm
        (f := S n) two_ne_zero ENNReal.ofNat_ne_top (hSL2 n))
    have hnormpow : (∫ ω, ‖S n ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, (S n ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      simp [Real.norm_eq_abs, sq_abs]
    rw [hLp2, hnormpow, ← variance_of_integral_eq_zero (MemLp.aemeasurable (hSL2 n)) (hSmean n)]
    have hpow : (variance (S n) μ) ^ (1 / (2 : ℝ))
        ≤ (∑' i, variance (X (i + 1)) μ) ^ (1 / (2 : ℝ)) :=
      Real.rpow_le_rpow (variance_nonneg (S n) μ) (hVarS_le n) (by positivity)
    simpa [Real.sqrt_eq_rpow] using ENNReal.ofReal_le_ofReal hpow
  have hbdd : ∃ R : NNReal, ∀ n, eLpNorm (S n) 1 μ ≤ R := by
    refine ⟨(ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ))).toNNReal, ?_⟩
    intro n
    have h12 : eLpNorm (S n) 1 μ ≤ eLpNorm (S n) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (show (1 : ENNReal) ≤ 2 by norm_num)
        (hSL2 n).aestronglyMeasurable
    have hbound : eLpNorm (S n) 1 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (X (i + 1)) μ)) :=
      h12.trans (hSL2_bound n)
    simpa [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top] using hbound
  rcases hbdd with ⟨R, hR⟩
  simpa [S] using (hSsub.exists_ae_tendsto_of_bdd hR)

lemma ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
    (hXm : ∀ i, StronglyMeasurable (X i)) (hXL2 : ∀ i, MemLp (X i) 2 μ) (hXind : iIndepFun X μ)
    (hXmean : ∀ i, μ[X i] = 0) (hVar : Summable (fun i => variance (X i) μ)) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Filter.Tendsto (fun n => ∑ i ∈ range n, X i ω) Filter.atTop (nhds c) := by
  have htail := ae_exists_tendsto_tailPartialSum_of_summable_variance_of_mean_zero
    (μ := μ) hXm hXL2 hXind (fun i => hXmean (i + 1)) ((summable_nat_add_iff 1).2 hVar)
  filter_upwards [htail] with ω hω
  rcases hω with ⟨c, hc⟩
  refine ⟨X 0 ω + c, ?_⟩
  have hsucc :
      Filter.Tendsto (fun n => ∑ i ∈ range (n + 1), X i ω) Filter.atTop (nhds (X 0 ω + c)) := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) ((hc.const_add (X 0 ω)))
    simpa [add_comm, add_left_comm, add_assoc] using
      (sum_range_succ' (f := fun i => X i ω) n).symm
  exact (Filter.tendsto_add_atTop_iff_nat
    (f := fun n => ∑ i ∈ range n, X i ω) (l := nhds (X 0 ω + c)) 1).1 hsucc

theorem kolmogorov_two_series
    (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i))
    (hXL2 : ∀ i, MemLp (X i) 2 μ)
    (hXind : iIndepFun X μ)
    (hMean : Summable (fun i => μ[X i]))
    (hVar : Summable (fun i => variance (X i) μ)) :
    ∀ᵐ ω ∂μ, ∃ x : ℝ,
      Filter.Tendsto (fun n => ∑ i ∈ range n, X i ω) Filter.atTop (nhds x) := by
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω - μ[X i]
  have hYm : ∀ i, StronglyMeasurable (Y i) := fun i ↦ (hXm i).sub stronglyMeasurable_const
  have hYL2 : ∀ i, MemLp (Y i) 2 μ := fun i ↦ MemLp.sub (hXL2 i) (memLp_const (∫ (x : Ω), X i x ∂μ))
  have hYind : iIndepFun Y μ := id (iIndepFun.comp hXind (fun i x ↦ x - ∫ (x : Ω), X i x ∂μ)
    fun i ↦ Measurable.sub measurable_id measurable_const)
  have hYmean : ∀ i, μ[Y i] = 0 := fun i ↦ by
    rw [integral_sub ((hXL2 i).integrable (by norm_num)) (integrable_const _), integral_const,
      probReal_univ, smul_eq_mul, one_mul, sub_self]
  have hYVar : Summable (fun i => variance (Y i) μ) := hVar.congr fun i ↦ Eq.symm <|
    variance_sub_const (StronglyMeasurable.aestronglyMeasurable (hXm i)) (∫ (x : Ω), X i x ∂μ)
  have hYconv := ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
    (μ := μ) hYm hYL2 hYind hYmean hYVar
  have hMeanConv :
      Filter.Tendsto (fun n => ∑ i ∈ range n, μ[X i]) Filter.atTop (nhds (∑' i, μ[X i])) :=
    hMean.hasSum.tendsto_sum_nat
  filter_upwards [hYconv] with ω hω
  rcases hω with ⟨c, hc⟩
  exact ⟨c + ∑' i, μ[X i], Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => by simp [Y])
    (hc.add hMeanConv)⟩


end
