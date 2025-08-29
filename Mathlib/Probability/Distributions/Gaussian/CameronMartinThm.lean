/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.CameronMartin
import Mathlib.Probability.HasLaw

/-!
# Cameron-Martin Theorem

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology InnerProductSpace

namespace MeasureTheory

variable {α ι E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f f' : ι → α → E} {g : α → E} {l : Filter ι}

lemma setIntegral_mono_on' {X : Type*} {mX : MeasurableSpace X}
    {μ : Measure X} {f g : X → ℝ} {s : Set X}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hs : NullMeasurableSet s μ) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm,
    setIntegral_congr_set hs.toMeasurable_ae_eq.symm]
  refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
  · rw [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
    exact hf
  · rw [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
    exact hg
  · exact measurableSet_toMeasurable μ s
  · filter_upwards [hs.toMeasurable_ae_eq.mem_iff] with x hx
    rw [hx]
    exact h x

lemma tendsto_of_limsup_measure_closed_le' {Ω ι : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    {L : Filter ι} [L.IsCountablyGenerated]
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ (μs i : Measure Ω) F) L ≤ (μ : Measure Ω) F) :
    Tendsto μs L (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]

-- lemma tendsto_of_limsup_measure_closed_le {Ω ι : Type*} [MeasurableSpace Ω]
--     [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]
--     {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
--     {L : Filter ι} [L.IsCountablyGenerated]
--     (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ μs i F) L ≤ μ F) :
--     Tendsto μs L (𝓝 μ) := by
--   sorry

theorem tendsto_iff_forall_lipschitz_integral_tendsto {γ Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {F : Filter γ} [F.IsCountablyGenerated]
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ (f : Ω → ℝ) (_ : ∃ (C : ℝ), ∀ x y, dist (f x) (f y) ≤ C) (_ : ∃ L, LipschitzWith L f),
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  constructor
  · intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω ℝ :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using h f'
  refine fun h ↦ tendsto_of_limsup_measure_closed_le' fun s hs ↦ ?_
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
  have key₁ : Tendsto (fun n ↦ ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) := by
    -- todo: extract lemma
    have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ hs (fun _ ↦ by positivity)
      (δs := fun n ↦ (1 : ℝ) / (n + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
    have h_eq (n : ℕ) : ∫⁻ ω, thickenedIndicator (δ := (1 : ℝ) / (n + 1)) (by positivity) s ω ∂μ
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
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ := h (fs M) ?_ ?_
  rotate_left
  · refine ⟨1, fun x y ↦ ?_⟩
    simp only [Real.dist_eq]
    rw [abs_le]
    have h1 x : fs M x ≤ 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 ≤ fs M x := by simp [fs]
    grind
  · exact ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s⟩
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' : ∀ᶠ x in F, (μs x : Measure Ω).real s ≤ ∫ a, fs M a ∂μ + ε / 2 := by
    refine ev_near.mono fun x hx ↦ le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ ?_ ?_
    · rw [integrable_indicator_iff hs.measurableSet]
      exact (integrable_const _).integrableOn
    · exact h_int _ _
    have h : _ ≤ fs M :=
      (indicator_le_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s)
    simpa using h
  apply (Filter.limsup_le_limsup ev_near' ?_ ?_).trans
  rotate_left
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)
  · exact isBoundedUnder_const
  rw [limsup_const]
  apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
  ring

lemma ProbabilityMeasure.todo [l.IsCountablyGenerated]
    (hf' : ∀ i, AEMeasurable (f' i) μ) (hf : ∀ i, AEMeasurable (f i) μ)
    (hg : AEMeasurable g μ) (hff' : TendstoInMeasure μ (fun n ↦ f' n - f n) l 0)
    (hfg : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (f n), isProbabilityMeasure_map (hf n)⟩) l
      (𝓝 ⟨μ.map g, isProbabilityMeasure_map hg⟩)) :
    Tendsto (β := ProbabilityMeasure E) (fun n ↦ ⟨μ.map (f' n), isProbabilityMeasure_map (hf' n)⟩) l
      (𝓝 ⟨μ.map g, isProbabilityMeasure_map hg⟩) := by
  rcases isEmpty_or_nonempty E with hE | hE
  · simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds
  let x₀ : E := hE.some
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ.map (f' n))) l (𝓝 (∫ ω, F ω ∂(μ.map g))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  by_cases hL : L = 0
  · simp only [hL] at hF_lip
    -- missing lemma `lipschitzWith_zero_iff`
    simp only [LipschitzWith, ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero,
      edist_eq_zero] at hF_lip
    specialize hF_lip x₀
    simp_rw [eq_comm (a := F x₀)] at hF_lip
    simp only [hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (f' n)) := isProbabilityMeasure_map (hf' n)
    have : IsProbabilityMeasure (μ.map g) := isProbabilityMeasure_map hg
    simp only [measureReal_univ_eq_one, one_mul]
    exact tendsto_const_nhds
  replace hL : 0 < L := lt_of_le_of_ne L.2 (Ne.symm hL)
  rw [Metric.tendsto_nhds]
  simp_rw [Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map g)| < L * ε by
    intro ε hε
    specialize this (ε / L) (by positivity)
    convert this
    field_simp
  intro ε hε
  have h_le n : |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map g)|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
        + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)| := by
    refine (dist_triangle (∫ ω, F ω ∂(μ.map (f' n))) (∫ ω, F ω ∂(μ.map (f n)))
      (∫ ω, F ω ∂(μ.map g))).trans ?_
    gcongr
    swap; · rw [Real.dist_eq]
    rw [Real.dist_eq]
    -- `⊢ |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map (f n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}`
    have h_int_f' : Integrable (fun x ↦ F (f' n x)) μ := by
      refine Integrable.of_bound ?_ (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      · exact AEStronglyMeasurable.comp_aemeasurable (by fun_prop) (hf' n)
      · specialize hF_bounded (f' n a) x₀
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (f' n a)) (F x₀)).trans hF_bounded
    have h_int_f : Integrable (fun x ↦ F (f n x)) μ := by
      refine Integrable.of_bound ?_ (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      · exact AEStronglyMeasurable.comp_aemeasurable (by fun_prop) (hf n)
      · specialize hF_bounded (f n a) x₀
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (f n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (f' n a) - F (f n a)‖) μ := by
      rw [integrable_norm_iff]
      · exact h_int_f'.sub h_int_f
      · refine AEStronglyMeasurable.sub ?_ ?_
        · exact AEStronglyMeasurable.comp_aemeasurable (by fun_prop) (hf' n)
        · exact AEStronglyMeasurable.comp_aemeasurable (by fun_prop) (hf n)
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_f' h_int_f]
    rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (f' n a) - F (f n a) ∂μ‖
    _ ≤ ∫ a, ‖F (f' n a) - F (f n a)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖f' n x - f n x‖ < ε / 2}, ‖F (f' n a) - F (f n a)‖ ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖f' n x - f n x‖}, ‖F (f' n a) - F (f n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ ?_
      · refine nullMeasurableSet_lt ?_ (by fun_prop)
        simp_rw [← dist_eq_norm]
        -- missing AEMeasurable.dist
        exact (@continuous_dist E _).aemeasurable2 (by fun_prop) (by fun_prop)
      · exact h_int_sub
    _ ≤ ∫ a in {x | ‖f' n x - f n x‖ < ε / 2}, L * (ε / 2) ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖f' n x - f n x‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on' ?_ ?_ ?_ ?_
        · exact h_int_sub.integrableOn
        · exact integrableOn_const
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · intro x hx
          simp only [Set.mem_setOf_eq] at hx
          rw [← dist_eq_norm] at hx ⊢
          exact hF_lip.dist_le_mul_of_le hx.le
      · refine setIntegral_mono ?_ ?_ fun a ↦ ?_
        · exact h_int_sub.integrableOn
        · exact integrableOn_const
        · rw [← dist_eq_norm]
          convert hF_bounded _ _
    _ = L * (ε / 2) * μ.real {x | ‖f' n x - f n x‖ < ε / 2}
        + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖} := by
      rw [mul_assoc]
      gcongr
      conv_rhs => rw [← mul_one (ε / 2)]
      gcongr
      exact measureReal_le_one
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
          + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
          + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine Tendsto.add ?_ ?_
    · refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
      · rw [mul_div_assoc]
        exact tendsto_const_nhds
      · simp only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] at hff'
        have h_tendsto := hff' (ε / 2) (by positivity) -- the result, up to `μ.real` vs `μ`
        refine Tendsto.comp ?_ h_tendsto
        exact ENNReal.tendsto_toReal (ENNReal.zero_ne_top)
    · simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hfg
      have h := hfg F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      rw [tendsto_iff_dist_tendsto_zero] at h
      simpa using h
  have h_lt : L * ε / 2 < L * ε := by
    rw [mul_div_assoc]
    gcongr
    exact half_lt_self hε
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`Tendsto` in the `ProbabilityMeasure` type). -/
lemma ProbabilityMeasure.tendsto_map_of_tendstoInMeasure [l.IsCountablyGenerated]
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : AEMeasurable g μ) (h : TendstoInMeasure μ f l g) :
    Tendsto (β := ProbabilityMeasure E) (fun n ↦ ⟨μ.map (f n), isProbabilityMeasure_map (hf n)⟩) l
      (𝓝 ⟨μ.map g, isProbabilityMeasure_map hg⟩) := by
  refine ProbabilityMeasure.todo hf (fun _ ↦ hg) hg ?_ tendsto_const_nhds
  simpa [tendstoInMeasure_iff_norm] using h

end MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

lemma hasLaw_cameronMartinRKHS (x : cameronMartinRKHS μ) :
    HasLaw x (gaussianReal 0 (‖x‖₊ ^ 2)) μ where
  map_eq := by
    by_cases hx0 : x = 0
    · simp only [hx0, ZeroMemClass.coe_zero, nnnorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, gaussianReal_zero_var]
      suffices μ.map (fun _ ↦ (0 : ℝ)) = Measure.dirac 0 by convert this; simp
      simp
    have hx_norm_pos : 0 < ‖x‖ := by simp [norm_pos_iff, hx0]
    unfold cameronMartinRKHS at x
    have h := x.2
    rw [Submodule.mem_topologicalClosure_iff, mem_closure_iff_seq_limit] at h
    obtain ⟨L, hL_mem, hL_tendsto⟩ := h
    simp only [Submodule.map_top, SetLike.mem_coe, LinearMap.mem_range] at hL_mem
    have hL_ne_zero : ∀ᶠ n in atTop, L n ≠ 0 := hL_tendsto.eventually_ne (by simp [hx0])
    let L' := fun n ↦ (‖x‖ / ‖L n‖) • L n
    have hL'_mem n : ∃ y, StrongDual.centeredToLp μ 2 y = L' n := by
      choose y' hy' using hL_mem
      refine ⟨(‖x‖ / ‖L n‖) • y' n, ?_⟩
      simp [hy' n, L']
    have hL'_tendsto : Tendsto L' atTop (𝓝 x) := by
      unfold L'
      have h_norm : Tendsto (fun n ↦ ‖L n‖) atTop (𝓝 ‖x‖) := hL_tendsto.norm
      suffices Tendsto (fun n ↦ (‖x‖ / ‖L n‖) • L n) atTop (𝓝 ((‖x‖ / ‖x‖) • x)) by
        rwa [div_self hx_norm_pos.ne', one_smul] at this
      refine Tendsto.smul ?_ hL_tendsto
      exact Tendsto.div tendsto_const_nhds h_norm hx_norm_pos.ne'
    choose y hy using hL'_mem
    have hy_map (n : ℕ) (hn : L n ≠ 0) : μ.map (y n) = gaussianReal (μ[y n]) (‖x‖₊ ^ 2) := by
      rw [IsGaussian.map_eq_gaussianReal]
      congr
      rw [← sq_norm_centeredToLp_two, hy n]
      unfold L'
      simp only [AddSubgroupClass.coe_norm, norm_smul, norm_div, norm_norm]
      rw [div_mul_cancel₀]
      · norm_cast
        rw [Real.toNNReal_pow (norm_nonneg _), norm_toNNReal]
      · simp [hn]
    have hL'_map n (hn : L n ≠ 0) : μ.map (L' n) = gaussianReal 0 (‖x‖₊ ^ 2) := by
      have h_eq : L' n =ᵐ[μ] fun x ↦ y n x - μ[y n] := by
        rw [← hy]
        filter_upwards [centeredToLp_apply (μ := μ) memLp_two_id (y n)] with z hz
        simp only [hz, map_sub, sub_right_inj]
        rw [IsGaussian.integral_dual]
      rw [Measure.map_congr h_eq]
      simpa using gaussianReal_sub_const' (hy_map n hn) (μ[y n])
    have hL'_prob n : IsProbabilityMeasure (μ.map (L' n)) := isProbabilityMeasure_map (by fun_prop)
    let ν n : ProbabilityMeasure ℝ := ⟨μ.map (L' n), hL'_prob n⟩
    have h_eventuallyEq : ∀ᶠ n in atTop, ν n = ⟨gaussianReal 0 (‖x‖₊ ^ 2), inferInstance⟩ := by
      filter_upwards [hL_ne_zero] with n hn
      unfold ν
      simp_rw [hL'_map n hn]
    have hν_tendsto_1 : Tendsto ν atTop (𝓝 ⟨gaussianReal 0 (‖x‖₊ ^ 2), inferInstance⟩) := by
      rw [tendsto_congr' h_eventuallyEq]
      exact tendsto_const_nhds
    have hx_prob : IsProbabilityMeasure (μ.map (x : E → ℝ)) :=
      isProbabilityMeasure_map (by fun_prop)
    have hν_tendsto_2 : Tendsto ν atTop (𝓝 ⟨μ.map x, hx_prob⟩) :=
      ProbabilityMeasure.tendsto_map_of_tendstoInMeasure (fun _ ↦ by fun_prop) (by fun_prop)
        (tendstoInMeasure_of_tendsto_Lp hL'_tendsto)
    have h_eq := tendsto_nhds_unique hν_tendsto_2 hν_tendsto_1
    rw [Subtype.ext_iff] at h_eq
    exact h_eq

lemma variance_cameronMartinRKHS (x : cameronMartinRKHS μ) :
    Var[x; μ] = ‖x‖₊ ^ 2 := by
  have : Var[fun y ↦ y; μ.map x] = ‖x‖₊ ^ 2 := by simp [(hasLaw_cameronMartinRKHS x).map_eq]
  rwa [variance_map aemeasurable_id' (by fun_prop)] at this

lemma covariance_cameronMartinRKHS (x y : cameronMartinRKHS μ) :
    cov[x, y; μ] = ⟪x, y⟫_ℝ := by
  rw [covariance_eq_variance_add_sub_div_two (Lp.memLp x.1) (Lp.memLp y.1)]
  have : (x : E → ℝ) + (y : E → ℝ) =ᵐ[μ] (x + y : cameronMartinRKHS μ) := by
    simp only [Submodule.coe_add, AddSubgroup.coe_add]
    exact (AEEqFun.coeFn_add _ _).symm
  rw [variance_congr this]
  simp_rw [variance_cameronMartinRKHS]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  simp [pow_two]

lemma isProbabilityMeasure_withDensity_cameronMartin (x : CameronMartin μ) :
    IsProbabilityMeasure (μ.withDensity fun y ↦
      .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) where
  measure_univ := by
    rw [withDensity_apply _ .univ, setLIntegral_univ]
    calc ∫⁻ a, .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) a - ‖x‖ ^ 2 / 2)) ∂μ
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2))
        * ∫⁻ a, .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) a)) ∂μ := by
      simp_rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [lintegral_mul_const _ (by fun_prop), mul_comm, neg_div]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2))
        * ∫⁻ a, .ofReal (.exp a) ∂(μ.map (cmIsometryEquiv μ x)) := by
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * ∫⁻ a, .ofReal (.exp a) ∂(gaussianReal 0 (‖x‖₊ ^ 2)) := by
      rw [(hasLaw_cameronMartinRKHS (cmIsometryEquiv μ x)).map_eq, (cmIsometryEquiv μ).nnnorm_map]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * .ofReal (.exp (‖x‖ ^ 2 / 2)) := by
      congr
      have h := mgf_id_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2)
      rw [funext_iff] at h
      specialize h 1
      simp only [mgf, id_eq, one_mul, mul_one, NNReal.coe_pow, coe_nnnorm, one_pow, zero_add] at h
      rw [← h, ofReal_integral_eq_lintegral_ofReal]
      · simpa using (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2) 1)
      · exact ae_of_all _ fun _ ↦ Real.exp_nonneg _
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      ring_nf
      simp

lemma todo_ae_eq (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    (cmIsometryEquiv μ (L - t • x) : E → ℝ)
      =ᵐ[μ] fun u ↦ L u - μ[L] - t * (cmIsometryEquiv μ x : E → ℝ) u := by
  simp only [map_sub, map_smul, AddSubgroupClass.coe_sub, cmIsometryEquiv_ofDual, SetLike.val_smul]
  filter_upwards [centeredToLp_apply (μ := μ) memLp_two_id L,
    AEEqFun.coeFn_sub (γ := ℝ) (StrongDual.centeredToLp μ 2 L) (t • (cmIsometryEquiv μ x)),
    Lp.coeFn_smul (E := ℝ) t (cmIsometryEquiv μ x : Lp ℝ 2 μ)] with u h_toLp h_sub h_smul
  simp only [SetLike.val_smul, Pi.sub_apply] at h_sub
  rw [h_sub, h_toLp, h_smul, IsGaussian.integral_dual]
  simp

lemma some_equality_in_Real'' (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (- ‖x‖ ^ 2 / 2)
        * ∫ u, exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * I + μ[L] * I) ∂μ := by
  calc ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I) ∂μ := by
    simp_rw [sub_eq_add_neg, exp_add]
    rw [integral_mul_const, mul_comm (exp _), neg_div]
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, exp ((L u - μ[L] - t * (cmIsometryEquiv μ x : E → ℝ) u) * I + μ[L] * I) ∂μ := by
    congr with u
    congr
    ring
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * I + μ[L] * I) ∂μ := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [todo_ae_eq x L t] with u hu
    rw [hu, integral_complex_ofReal]
    simp

lemma some_equality_in_Real' (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
        * ∫ u : ℝ, exp (u * I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
  calc ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * I + μ[L] * I) ∂μ :=
    some_equality_in_Real'' x L t
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u : ℝ, exp (u * I + μ[L] * I) ∂(μ.map (cmIsometryEquiv μ (L - t • x))) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = exp (- ‖x‖ ^ 2 / 2)
      * ∫ u : ℝ, exp (u * I + μ[L] * I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
    rw [(hasLaw_cameronMartinRKHS (cmIsometryEquiv μ (L - t • x))).map_eq,
      (cmIsometryEquiv μ).nnnorm_map]
  _ = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
      * ∫ u : ℝ, exp (u * I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
    rw [exp_add, mul_assoc]
    congr 1
    simp_rw [exp_add]
    rw [integral_mul_const, mul_comm _ (exp _)]

lemma some_equality_in_Real (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2
        + μ[L] * I - Var[L; μ] / 2) := by
  calc ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
  _ = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
      * ∫ u : ℝ, exp (u * I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := some_equality_in_Real' x L t
  _ = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I - ‖L - t • x‖ ^ 2 / 2) := by
    conv_lhs => rw [exp_add]
    conv_rhs => rw [add_sub_assoc, exp_add, sub_eq_add_neg, exp_add, ← mul_assoc]
    have h := charFun_gaussianReal (μ := 0) (v := ‖L - t • x‖₊ ^ 2) 1
    simp only [charFun, RCLike.inner_apply, conj_trivial, one_mul, Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_pow, coe_nnnorm, Complex.ofReal_pow,
      one_pow, mul_one, zero_sub] at h
    rw [h]
  _ = exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) := by
    have h_inner : (t : ℂ) * L x.toInitialSpace = ⟪.ofDual μ L, t • x⟫_ℝ := by
      simp [← CameronMartin.apply_toInitialSpace_eq_inner]
    rw [h_inner, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    simp_rw [← pow_two]
    rw [CameronMartin.sq_norm_ofDual (μ := μ) L]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring_nf

lemma todo_hasDerivAt (x : CameronMartin μ) (L : StrongDual ℝ E) (z : ℂ) :
    HasDerivAt
      (fun z ↦ ∫ u, exp ((L u - z * (cmIsometryEquiv μ x : E → ℝ) u) * I) ∂μ)
      (∫ u, - (cmIsometryEquiv μ x : E → ℝ) u * I
        * exp ((L u - z * (cmIsometryEquiv μ x : E → ℝ) u) * I) ∂μ) z := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |(cmIsometryEquiv μ x : E → ℝ) ω|
      * Real.exp (z.im * (cmIsometryEquiv μ x : E → ℝ) ω + |(cmIsometryEquiv μ x : E → ℝ) ω|))
    (F := fun z ω ↦ cexp ((L ω - z * (cmIsometryEquiv μ x : E → ℝ) ω) * I))
    (F' := fun z ω ↦ - (cmIsometryEquiv μ x : E → ℝ) ω * I
        * exp ((L ω - z * (cmIsometryEquiv μ x : E → ℝ) ω) * I)) zero_lt_one ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z ↦ by fun_prop
  · rw [← integrable_norm_iff (by fun_prop)]
    simp only [norm_exp, mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, sub_im,
      mul_im, zero_add, zero_sub, I_im, mul_one, sub_neg_eq_add]
    change Integrable ((fun a ↦ Real.exp (z.im * a)) ∘ (cmIsometryEquiv μ x : E → ℝ)) μ
    rw [← integrable_map_measure (f := fun ω ↦ (cmIsometryEquiv μ x : E → ℝ) ω) (by fun_prop)
      (by fun_prop), (hasLaw_cameronMartinRKHS (cmIsometryEquiv μ x)).map_eq]
    exact integrable_exp_mul_gaussianReal (μ := 0) (v := ‖cmIsometryEquiv μ x‖₊ ^ 2) z.im
  · fun_prop
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only [neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    rw [Complex.norm_exp]
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, sub_im, mul_im,
      zero_add, zero_sub, I_im, mul_one, sub_neg_eq_add]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this, add_im, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    conv_rhs => rw [← one_mul (|(cmIsometryEquiv μ x : E → ℝ) ω|)]
    gcongr
    refine (abs_im_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · change Integrable
      ((fun ω ↦ |ω| * Real.exp (z.im * ω + |ω|)) ∘ (cmIsometryEquiv μ x : E → ℝ)) μ
    rw [← integrable_map_measure (f := fun ω ↦ (cmIsometryEquiv μ x : E → ℝ) ω) (by fun_prop)
      (by fun_prop), (hasLaw_cameronMartinRKHS (cmIsometryEquiv μ x)).map_eq]
    have h := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul (x := 1) (v := z.im) (X := id)
      (t := 2) (μ := gaussianReal 0 (‖cmIsometryEquiv μ x‖₊ ^ 2)) ?_ ?_ zero_le_one (by simp) 1
    · simpa only [id_eq, pow_one, one_mul] using h
    · exact integrable_exp_mul_gaussianReal (z.im + 2)
    · exact integrable_exp_mul_gaussianReal (z.im - 2)
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only
    simp_rw [sub_mul, sub_eq_add_neg, exp_add, ← neg_mul, mul_comm (_ * I), mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [neg_mul, mul_comm _ (_ * I), ← neg_mul]
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_ℂ]
    convert hasDerivAt_exp_smul_const (-(cmIsometryEquiv μ x : E → ℝ) ω * I : ℂ) ε using 1
    · ext ω
      congr 1
      simp only [smul_eq_mul, neg_mul, mul_neg, neg_inj]
      ring
    · simp only [smul_eq_mul, neg_mul, mul_neg, neg_inj, mul_eq_mul_right_iff, mul_eq_zero,
        ofReal_eq_zero, I_ne_zero, or_false]
      left
      congr 2
      ring

lemma todo_analytic (x : CameronMartin μ) (L : StrongDual ℝ E) :
    AnalyticOnNhd ℂ
      (fun z ↦ ∫ u, exp ((L u - z * (cmIsometryEquiv μ x : E → ℝ) u) * I) ∂μ) Set.univ := by
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) isOpen_univ
  have h := todo_hasDerivAt x L z
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

lemma some_equality_in_Complex (x : CameronMartin μ) (L : StrongDual ℝ E) (z : ℂ) :
    ∫ u, exp ((L u - z * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (z * L x.toInitialSpace - (1 + z ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) := by
  revert z
  refine funext_iff.mp ?_
  rw [← Set.eqOn_univ]
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (𝕜 := ℂ) (E := ℂ) (z₀ := 0) ?_ ?_
    isPreconnected_univ (Set.mem_univ 0) ?_
  · simp_rw [sub_eq_add_neg, exp_add, integral_mul_const]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    simp_rw [← sub_eq_add_neg]
    exact todo_analytic _ _
  · simp_rw [sub_eq_add_neg, exp_add]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ ?_
    · exact (analyticOnNhd_id.mul analyticOnNhd_const).cexp
    · refine (AnalyticOnNhd.mul ?_ analyticOnNhd_const).neg.cexp
      exact (analyticOnNhd_const.add (analyticOnNhd_id.pow 2)).mul analyticOnNhd_const
  -- todo: extract lemma: frequently around a point in ℝ implies frequently around the point in ℂ.
  -- This is also used in ComplexMGF
  have h_real : ∃ᶠ (t : ℝ) in 𝓝[≠] 0,
      ∫ u, exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * I - ‖x‖ ^ 2 / 2) ∂μ
        = .exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) :=
    .of_forall fun y ↦ some_equality_in_Real x L y
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [← Complex.ofReal_zero, tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

lemma cor_for_z_eq_I (x : CameronMartin μ) (L : StrongDual ℝ E) :
    ∫ u, exp (L u * I + (cmIsometryEquiv μ x : E → ℝ) u - ‖x‖ ^ 2 / 2) ∂μ
      = exp ((μ[L] + L x.toInitialSpace) * I - Var[L; μ] / 2) := by
  have h := some_equality_in_Complex x L I
  simp only [I_sq, add_neg_cancel, zero_div, zero_mul, sub_zero] at h
  convert h using 3
  · congr
    rw [mul_comm I, sub_mul, mul_assoc]
    simp
  · ring

lemma charFunDual_withDensity_cameronMartin (x : CameronMartin μ) (L : StrongDual ℝ E) :
    charFunDual
        (μ.withDensity fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) L
      = exp ((μ[L] + L x.toInitialSpace) * I - Var[L; μ] / 2) := by
  calc charFunDual
        (μ.withDensity fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) L
  _ = ∫ u, exp (L u * I + (cmIsometryEquiv μ x : E → ℝ) u - ‖x‖ ^ 2 / 2) ∂μ := by
    rw [charFunDual_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
    swap; · exact ae_of_all _ (by finiteness)
    congr with u
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), add_sub_assoc, exp_add,
      mul_comm (exp _)]
    simp
  _ = exp ((μ[L] + L x.toInitialSpace) * I - Var[L; μ] / 2) := cor_for_z_eq_I x L

theorem map_add_cameronMartin_eq_withDensity (x : CameronMartin μ) :
    μ.map (fun y ↦ y + x.toInitialSpace)
      = μ.withDensity (fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) := by
  have := isProbabilityMeasure_withDensity_cameronMartin x
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_map_add_const, IsGaussian.charFunDual_eq, ← exp_add,
    charFunDual_withDensity_cameronMartin x L]
  congr
  ring

theorem absolutelyContinuous_map_add_cameronMartin (x : CameronMartin μ) :
    μ.map (fun y ↦ y + x.toInitialSpace) ≪ μ := by
  rw [map_add_cameronMartin_eq_withDensity x]
  exact withDensity_absolutelyContinuous _ _

-- defined in another PR. We state its properties here with `sorry` proofs, but they are all proved
-- there.
def tvDist (μ ν : Measure E) : ℝ := sorry

lemma tvDist_le_one {μ ν : Measure E} : tvDist μ ν ≤ 1 := by
  sorry

lemma mutuallySingular_iff_tvDist_eq_one {μ ν : Measure E} :
    μ ⟂ₘ ν ↔ tvDist μ ν = 1 := by
  sorry

lemma tvDist_map_le {F : Type*} {mF : MeasurableSpace F} {μ ν : Measure E}
    {f : E → F} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  sorry

lemma one_sub_exp_le_tvDist_gaussianReal (μ₁ μ₂ : ℝ) :
    1 - Real.exp (- (μ₁ - μ₂) ^ 2 / 8) ≤ tvDist (gaussianReal μ₁ 1) (gaussianReal μ₂ 1) := by
  sorry

lemma tvDist_dirac_of_ne {x y : E} (hxy : x ≠ y) :
    tvDist (Measure.dirac x) (Measure.dirac y) = 1 := by
  sorry

lemma gaussianReal_ext_iff {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    gaussianReal μ₁ v₁ = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁),
    ← integral_id_gaussianReal (μ := μ₂) (v := v₂), h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : ℝ) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁),
    ← variance_id_gaussianReal (μ := μ₂) (v := v₂), h]

lemma mutuallySingular_map_add_of_notMem_range_toInitialSpace (y : E)
    (hy : y ∉ Set.range (CameronMartin.toInitialSpace (μ := μ))) :
    μ.map (fun z ↦ z + y) ⟂ₘ μ := by
  rw [mutuallySingular_iff_tvDist_eq_one]
  refine le_antisymm tvDist_le_one ?_
  refine le_of_forall_lt fun c hc ↦ ?_
  obtain ⟨n, hcn⟩ : ∃ n : ℕ, c < 1 - Real.exp (- n ^ 2 / 8) := by
    simp_rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt']
    suffices Tendsto (fun n : ℕ ↦ Real.exp (- n ^ 2 / 8)) atTop (𝓝 0) by
      refine Eventually.exists (f := atTop) ?_
      refine this.eventually_lt_const ?_
      grind
    change Tendsto ((fun x : ℝ ↦ Real.exp (- x ^ 2 / 8)) ∘ (Nat.cast : ℕ → ℝ)) atTop (𝓝 0)
    refine Tendsto.comp ?_ <| tendsto_natCast_atTop_atTop (R := ℝ)
    simp [tendsto_div_const_atBot_iff]
  refine hcn.trans_le ?_
  obtain ⟨L, hL_var, hL_lt⟩ : ∃ L : StrongDual ℝ E, (Var[L; μ] = 1 ∨ Var[L; μ] = 0) ∧ n < L y := by
    simp only [CameronMartin.range_toInitialSpace, Set.mem_setOf_eq, not_exists, not_forall,
      not_le] at hy
    obtain ⟨L, hL_var, hL_lt⟩ := hy n
    by_cases hL_var_zero : Var[L; μ] = 0
    · exact ⟨L, Or.inr hL_var_zero, hL_lt⟩
    have h_var_pos : 0 < Var[L; μ] := by
      refine (variance_nonneg _ _).lt_of_ne' hL_var_zero
    refine ⟨√Var[L; μ]⁻¹ • L, ?_, ?_⟩
    · left
      simp only [ContinuousLinearMap.coe_smul']
      rw [variance_smul, Real.sq_sqrt, inv_mul_cancel₀]
      · exact h_var_pos.ne'
      · simp [variance_nonneg]
    · refine hL_lt.trans_le ?_
      simp only [Real.sqrt_inv, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      conv_lhs => rw [← one_mul (L y)]
      gcongr
      · exact le_trans (by positivity) hL_lt.le
      · rw [one_le_inv_iff₀, Real.sqrt_pos, Real.sqrt_le_one]
        simp [hL_var, h_var_pos]
  have h_le : tvDist ((μ.map (fun z ↦ z + y)).map L) (μ.map L)
      ≤ tvDist (μ.map (fun z ↦ z + y)) μ := tvDist_map_le (by fun_prop)
  refine le_trans ?_ h_le
  simp only [IsGaussian.map_eq_gaussianReal]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [map_add]
  rw [integral_add (by fun_prop) (by fun_prop), variance_map (by fun_prop) (by fun_prop)]
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  have : L ∘ (fun z ↦ z + y) = fun z ↦ L z + L y := by ext; simp
  rw [this, variance_add_const (by fun_prop)]
  by_cases hL_var_zero : Var[L; μ] = 0
  · simp only [hL_var_zero, Real.toNNReal_zero, gaussianReal_zero_var, tsub_le_iff_right,
      ge_iff_le]
    rw [tvDist_dirac_of_ne]
    · simp only [le_add_iff_nonneg_right]
      positivity
    · simp only [ne_eq, add_eq_left]
      have : (0 : ℝ) ≤ n := by positivity
      exact (this.trans_lt hL_lt).ne'
  · simp only [hL_var_zero, or_false] at hL_var
    simp only [hL_var, Real.toNNReal_one]
    refine le_trans ?_ (one_sub_exp_le_tvDist_gaussianReal (μ[L] + L y) μ[L])
    gcongr
    ring_nf
    exact hL_lt.le

end ProbabilityTheory
