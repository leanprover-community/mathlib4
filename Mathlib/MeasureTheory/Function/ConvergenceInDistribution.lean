/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.IdentDistrib

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

We also state results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution.

## Main definitions

* `TendstoInDistribution X l Z μ`: the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
* `tendstoInDistribution_of_tendstoInMeasure_sub`: the main technical tool for the next results.
  Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
  to `Z`, and `Y n - X n` converges in probability to `0`.
  Then `Y n` converges in distribution to `Z`.
* `TendstoInMeasure.tendstoInDistribution`: convergence in probability implies convergence in
  distribution.
* `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`: **Slutsky's theorem**.
  If `X n` converges in distribution to `Z`, and `Y n` converges in probability to a constant `c`,
  then the pair `(X n, Y n)` converges in distribution to `(Z, c)`.
* `tendstoInDistribution_of_approx`: **Billingsley's approximation theorem**.
  If `X k n` converges in distribution to `Y k` as `n → ∞` for each `k`, `Y k` converges in
  distribution to `Z` as `k → ∞`, and `X k n` approximates `U n` in probability, uniformly in
  `n` as `k → ∞`, then `U n` converges in distribution to `Z`.

-/

public section

open Filter ProbabilityTheory BoundedContinuousFunction
open scoped Topology

namespace MeasureTheory

variable {ι E Ω' Ω'' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

section TendstoInDistribution

variable [TopologicalSpace E]

/-- Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in the
`ProbabilityMeasure` type. -/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), inferInstance⟩) l (𝓝 ⟨μ'.map Z, inferInstance⟩)

theorem tendstoInDistribution_iff_forall_integral_rclike_tendsto
    (𝕜 : Type*) [RCLike 𝕜] [OpensMeasurableSpace E]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ f : E →ᵇ 𝕜, Tendsto (fun i ↦ ∫ ω, f (X i ω) ∂(μ i)) l (𝓝 (∫ ω, f (Z ω) ∂μ')) := by
  have h_map (i) (f : E →ᵇ 𝕜) :
      ∫ x, f x ∂(μ i).map (X i) = ∫ ω, f (X i ω) ∂(μ i) := integral_map (hX i) (by fun_prop)
  have h_map' (f : E →ᵇ 𝕜) :
      ∫ x, f x ∂μ'.map Z = ∫ ω, f (Z ω) ∂μ' := integral_map hZ (by fun_prop)
  refine ⟨fun h f ↦ ?_, fun h ↦ ⟨hX, hZ, ?_⟩⟩
  · have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp h.tendsto f
    simpa [h_map, h_map'] using hf
  · apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto (Ω := E) 𝕜).mpr
    intro f
    simpa [h_map, h_map'] using h f

lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ') :
    TendstoInDistribution (fun _ ↦ Z) l Z (fun _ ↦ μ') μ' where
  forall_aemeasurable := fun _ ↦ by fun_prop
  tendsto := tendsto_const_nhds

set_option backward.isDefEq.respectTransparency.types false in
lemma tendstoInDistribution_of_identDistrib [OpensMeasurableSpace E] (i : ι)
    (hX : ∀ j, IdentDistrib (X i) (X j) (μ i) (μ j)) (hZ : IdentDistrib (X i) Z (μ i) μ') :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable j := (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert! tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq

set_option backward.isDefEq.respectTransparency.types false in
protected lemma TendstoInDistribution.congr [OpensMeasurableSpace E] {T : Ω' → E}
    (hXY : ∀ i, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable i := (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert! h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

@[simp]
lemma tendstoInDistribution_of_isEmpty [IsEmpty E] :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable := fun _ ↦ (measurable_of_subsingleton_codomain _).aemeasurable
  aemeasurable_limit := (measurable_of_subsingleton_codomain _).aemeasurable
  tendsto := by
    simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds

set_option backward.isDefEq.respectTransparency false in
lemma tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E]
    (X : (i : ι) → Ω i → E) {Z : Ω' → E} {W : Ω'' → E} [l.NeBot]
    (h1 : TendstoInDistribution X l Z μ μ') (h2 : TendstoInDistribution X l W μ μ'') :
    μ'.map Z = μ''.map W := by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

set_option backward.isDefEq.respectTransparency.types false in
/-- **Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution. -/
theorem TendstoInDistribution.continuous_comp {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E → F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ μ' where
  forall_aemeasurable := fun n ↦ hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

set_option backward.isDefEq.respectTransparency.types false in
/-- Almost sure convergence implies convergence in distribution. -/
theorem tendstoInDistribution_of_ae_tendsto [l.IsCountablyGenerated]
    [OpensMeasurableSpace E] {X : ι → Ω' → E}
    (hX₁ : ∀ i, AEMeasurable (X i) μ') (hZ : AEMeasurable Z μ')
    (hX₂ : ∀ᵐ ω ∂μ', Tendsto (fun i ↦ X i ω) l (𝓝 (Z ω))) :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' where
  forall_aemeasurable := hX₁
  aemeasurable_limit := hZ
  tendsto := by
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, ProbabilityMeasure.coe_mk]
    intro f
    rw [lintegral_map' (by fun_prop) hZ]
    conv in ∫⁻ _, _ ∂_ => rw [lintegral_map' (by fun_prop) (hX₁ i)]
    apply tendsto_lintegral_filter_of_dominated_convergence' (bound := fun _ ↦ edist 0 f)
    · exact .of_forall (by fun_prop)
    · simp [f.apply_le_edist_zero]
    · simp
    filter_upwards [hX₂] with ω hω
    simpa [Function.comp_def] using f.continuous.tendsto (Z ω) |>.comp hω

end TendstoInDistribution

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`TendstoInDistribution`). -/
theorem TendstoInMeasure.tendstoInDistribution [PseudoEMetricSpace E] [BorelSpace E]
    [l.IsCountablyGenerated] [l.NeBot] {X : ι → Ω' → E}
    (h : TendstoInMeasure μ' X l Z) (hX : ∀ i, AEMeasurable (X i) μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' := by
  have hZ := h.aemeasurable hX
  refine ⟨hX, hZ, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  obtain ⟨ms, hms1, hms2⟩ := h.comp hns |>.exists_seq_tendsto_ae'
  refine ⟨ms, TendstoInDistribution.tendsto ?_⟩
  exact tendstoInDistribution_of_ae_tendsto (by fun_prop) hZ hms2

/-- Convergence in distribution can be tested on bounded Lipschitz functions. -/
theorem tendstoInDistribution_iff_forall_lipschitz_integral_tendsto [PseudoEMetricSpace E]
    [OpensMeasurableSpace E] [l.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ F : E → ℝ, (∃ C, ∀ x y, dist (F x) (F y) ≤ C) → (∃ L, LipschitzWith L F) →
        Tendsto (fun i ↦ ∫ ω, F (X i ω) ∂(μ i)) l (𝓝 (∫ ω, F (Z ω) ∂μ')) := by
  have h_map (i) {F : E → ℝ} (hF : Continuous F) :
      ∫ x, F x ∂(μ i).map (X i) = ∫ ω, F (X i ω) ∂(μ i) :=
    integral_map (hX i) hF.aestronglyMeasurable
  have h_map' {F : E → ℝ} (hF : Continuous F) : ∫ x, F x ∂μ'.map Z = ∫ ω, F (Z ω) ∂μ' :=
    integral_map hZ hF.aestronglyMeasurable
  refine ⟨fun h F hF_bounded hF_lip ↦ ?_, fun h ↦ ⟨hX, hZ, ?_⟩⟩
  · have hF := (tendsto_iff_forall_lipschitz_integral_tendsto.mp h.tendsto) F hF_bounded hF_lip
    have hF_cont : Continuous F := hF_lip.choose_spec.continuous
    simpa [h_map _ hF_cont, h_map' hF_cont] using hF
  · refine tendsto_iff_forall_lipschitz_integral_tendsto.mpr fun F hF_bounded hF_lip ↦ ?_
    have hF_cont : Continuous F := hF_lip.choose_spec.continuous
    simpa [h_map _ hF_cont, h_map' hF_cont] using h F hF_bounded hF_lip

section Approximation

variable [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]

/-- Let `F` be an `L`-Lipschitz real function whose oscillation is bounded by `M`, and let `A, B`
be two random variables on the same probability space. Then for `δ ≥ 0`,
`|𝔼[F ∘ A] - 𝔼[F ∘ B]| ≤ L * δ + M * ℙ(δ ≤ dist A B)`. -/
lemma abs_integral_sub_integral_le_of_lipschitzWith {A B : Ω'' → E}
    (hA : AEMeasurable A μ'') (hB : AEMeasurable B μ'') {F : E → ℝ} {M : ℝ}
    (hF_bounded : ∀ x y, dist (F x) (F y) ≤ M) {L : NNReal} (hF_lip : LipschitzWith L F) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    |∫ ω, F (A ω) ∂μ'' - ∫ ω, F (B ω) ∂μ''|
      ≤ L * δ + M * μ''.real {ω | δ ≤ dist (A ω) (B ω)} := by
  let f : E →ᵇ ℝ := .mkOfBound ⟨F, hF_lip.continuous⟩ M hF_bounded
  have h_int_A : Integrable (fun ω ↦ F (A ω)) μ'' :=
    (f.integrable (μ''.map A)).comp_aemeasurable hA
  have h_int_B : Integrable (fun ω ↦ F (B ω)) μ'' :=
    (f.integrable (μ''.map B)).comp_aemeasurable hB
  have h_int_sub : Integrable (fun ω ↦ ‖F (A ω) - F (B ω)‖) μ'' := (h_int_A.sub h_int_B).norm
  have h_meas : NullMeasurableSet {ω | dist (A ω) (B ω) < δ} μ'' :=
    nullMeasurableSet_lt (by fun_prop) (by fun_prop)
  rw [← integral_sub h_int_A h_int_B, ← Real.norm_eq_abs]
  calc ‖∫ ω, F (A ω) - F (B ω) ∂μ''‖
  _ ≤ ∫ ω, ‖F (A ω) - F (B ω)‖ ∂μ'' := norm_integral_le_integral_norm _
  -- Either `dist (A ω) (B ω)` is smaller than `δ`, or it is not
  _ = ∫ ω in {ω | dist (A ω) (B ω) < δ}, ‖F (A ω) - F (B ω)‖ ∂μ''
      + ∫ ω in {ω | δ ≤ dist (A ω) (B ω)}, ‖F (A ω) - F (B ω)‖ ∂μ'' := by
    simp_rw [← not_lt]
    exact (integral_add_compl₀ h_meas h_int_sub).symm
  -- If it is smaller, we use the Lipschitz property of `F`; if not, the boundedness of `F`
  _ ≤ ∫ ω in {ω | dist (A ω) (B ω) < δ}, L * δ ∂μ''
      + ∫ ω in {ω | δ ≤ dist (A ω) (B ω)}, M ∂μ'' := by
    gcongr ?_ + ?_
    · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const h_meas ?_
      intro ω (hω : dist (A ω) (B ω) < δ)
      rw [← dist_eq_norm]
      exact (hF_lip.dist_le_mul _ _).trans (by gcongr)
    · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun ω ↦ ?_
      rw [← dist_eq_norm]
      exact hF_bounded _ _
  _ = L * δ * μ''.real {ω | dist (A ω) (B ω) < δ}
      + M * μ''.real {ω | δ ≤ dist (A ω) (B ω)} := by
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
      smul_eq_mul]
    ring
  _ ≤ L * δ + M * μ''.real {ω | δ ≤ dist (A ω) (B ω)} := by
    rw [mul_assoc]
    gcongr
    grw [measureReal_le_one, mul_one]

/-- **Approximation theorem for convergence in distribution** (Billingsley, *Convergence of
Probability Measures*, 2nd ed., Theorem 3.2).

Let `U i` be random variables, and for each `k` let `X k i` be random variables defined on the
same probability spaces as `U i`. Suppose that
* for each `k`, `X k i` converges in distribution to `Y k` along `l`;
* `Y k` converges in distribution to `Z` along `l'`;
* the `X k` approximate `U` uniformly in probability: for every `δ > 0`,
  `limsup_{i → l} ℙ(δ ≤ dist (U i) (X k i))` tends to `0` along `l'`.

Then `U i` converges in distribution to `Z` along `l`.

Taking `X k = X`, `Y k = Z` for all `k` recovers `tendstoInDistribution_of_tendstoInMeasure_sub`
(for random variables defined on a common probability space). -/
theorem tendstoInDistribution_of_approx {κ : Type*} {Ωκ : κ → Type*}
    {mκ : ∀ k, MeasurableSpace (Ωκ k)} {ν : (k : κ) → Measure (Ωκ k)}
    [∀ k, IsProbabilityMeasure (ν k)] {l' : Filter κ} [l'.NeBot] [l.IsCountablyGenerated]
    {X : κ → (i : ι) → Ω i → E} {Y : (k : κ) → Ωκ k → E} {U : (i : ι) → Ω i → E}
    (hX : ∀ k, TendstoInDistribution (X k) l (Y k) μ (ν k))
    (hY : TendstoInDistribution Y l' Z ν μ') (hU : ∀ i, AEMeasurable (U i) (μ i))
    (h_approx : ∀ δ > 0, Tendsto
      (fun k ↦ limsup (fun i ↦ μ i {ω | δ ≤ dist (U i ω) (X k i ω)}) l) l' (𝓝 0)) :
    TendstoInDistribution U l Z μ μ' := by
  rw [tendstoInDistribution_iff_forall_lipschitz_integral_tendsto hU hY.aemeasurable_limit]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hM : 0 ≤ M := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ'
    exact dist_nonneg.trans (hF_bounded (Z ω) (Z ω))
  -- Convergence in distribution, tested against the bounded continuous function `F`
  let f : E →ᵇ ℝ := .mkOfBound ⟨F, hF_lip.continuous⟩ M hF_bounded
  have h_Y : Tendsto (fun k ↦ ∫ ω, F (Y k ω) ∂(ν k)) l' (𝓝 (∫ ω, F (Z ω) ∂μ')) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hY.forall_aemeasurable
      hY.aemeasurable_limit).mp hY f
  rw [Metric.tendsto_nhds]
  intro η hη
  -- We split `η` into four pieces: `L * δ < η / 4`, `M * ε ≤ η / 4`, and two more for the
  -- convergence in distribution of `X k` and of `Y`.
  set δ : ℝ := η / (4 * ((L : ℝ) + 1)) with hδ_def
  set ε : ℝ := η / (4 * (M + 1)) with hε_def
  have hδ : 0 < δ := by positivity
  have hε : 0 < ε := by positivity
  have hLδ : L * δ < η / 4 := by
    rw [hδ_def, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hMε : M * ε ≤ η / 4 := by
    rw [hε_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- Choose `k` such that `Y k` is close to `Z` and `X k` approximates `U` well
  obtain ⟨k, hk_approx, hk_Y⟩ := ((h_approx δ hδ).eventually_lt_const
    (ENNReal.ofReal_pos.mpr hε)).and
    (Metric.tendsto_nhds.mp h_Y (η / 4) (by positivity)) |>.exists
  -- Bound the integrals for that `k`
  have h_Yk : Tendsto (fun i ↦ ∫ ω, F (X k i ω) ∂(μ i)) l (𝓝 (∫ ω, F (Y k ω) ∂(ν k))) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ (hX k).forall_aemeasurable
      (hX k).aemeasurable_limit).mp (hX k) f
  filter_upwards [eventually_lt_of_limsup_lt hk_approx,
    Metric.tendsto_nhds.mp h_Yk (η / 4) (by positivity)] with i hi_approx hi_X
  have h_UX := abs_integral_sub_integral_le_of_lipschitzWith (hU i)
    ((hX k).forall_aemeasurable i) hF_bounded hF_lip hδ.le
  have h_meas : (μ i).real {ω | δ ≤ dist (U i ω) (X k i ω)} < ε :=
    ENNReal.toReal_lt_of_lt_ofReal hi_approx
  rw [Real.dist_eq] at hi_X hk_Y ⊢
  calc |∫ ω, F (U i ω) ∂(μ i) - ∫ ω, F (Z ω) ∂μ'|
  _ ≤ |∫ ω, F (U i ω) ∂(μ i) - ∫ ω, F (X k i ω) ∂(μ i)|
      + |∫ ω, F (X k i ω) ∂(μ i) - ∫ ω, F (Y k ω) ∂(ν k)|
      + |∫ ω, F (Y k ω) ∂(ν k) - ∫ ω, F (Z ω) ∂μ'| := by
    grw [abs_sub_le _ (∫ ω, F (X k i ω) ∂(μ i)) _, add_assoc,
      abs_sub_le (∫ ω, F (X k i ω) ∂(μ i)) (∫ ω, F (Y k ω) ∂(ν k)) _]
  _ < η := by
    have := mul_le_mul_of_nonneg_left h_meas.le hM
    linarith

end Approximation

variable [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
to `Z`, and `Y n - X n` converges in probability to `0`.
Then `Y n` converges in distribution to `Z`. -/
lemma tendstoInDistribution_of_tendstoInMeasure_sub {X : ι → Ω'' → E}
    [l.IsCountablyGenerated] (Y : ι → Ω'' → E) (Z : Ω' → E)
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ') (hXY : TendstoInMeasure μ'' (Y - X) l 0)
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ''.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n))) (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    rw [integral_map (hY n) hF_cont.aestronglyMeasurable,
      integral_map (hX n) hF_cont.aestronglyMeasurable]
    simpa only [dist_eq_norm] using abs_integral_sub_integral_le_of_lipschitzWith (hY n) (hX n)
      hF_bounded hF_lip (δ := ε / 2) (by positivity)
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`TendstoInDistribution`). -/
lemma TendstoInMeasure.tendstoInDistribution_of_aemeasurable [l.IsCountablyGenerated]
    {X : ι → Ω' → E} (h : TendstoInMeasure μ' X l Z) (hX : ∀ i, AEMeasurable (X i) μ')
    (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' :=
  tendstoInDistribution_of_tendstoInMeasure_sub X Z (tendstoInDistribution_const hZ)
    (by simpa [tendstoInMeasure_iff_norm] using h) hX

/-- **Slutsky's theorem**: if `X n` converges in distribution to `Z`, and `Y n` converges in
probability to a constant `c`, then the pair `(X n, Y n)` converges in distribution to `(Z, c)`. -/
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    {E' : Type*} {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [l.IsCountablyGenerated] (X : ι → Ω'' → E) (Y : ι → Ω'' → E') (Z : Ω' → E)
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) (fun _ ↦ μ'') μ' := by
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω ↦ (X n ω, c))
    (fun n ω ↦ (X n ω, Y n ω)) (fun ω ↦ (Z ω, c)) ?_ ?_ (fun i ↦ (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x ↦ (x, c)) (by fun_prop)
  · suffices TendstoInMeasure μ'' (fun n ω ↦ ((0 : E), Y n ω - c)) l 0 by
      convert! this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

/-- **Slutsky's theorem** for a continuous function: if `X n` converges in distribution to `Z`,
`Y n` converges in probability to a constant `c`, and `g` is a continuous function, then
`g (X n, Y n)` converges in distribution to `g (Z, c)`. -/
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const {E' F : Type*}
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E × E' → F} (hg : Continuous g)
    [l.IsCountablyGenerated] {X : ι → Ω'' → E} {Y : ι → Ω'' → E'}
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l (fun ω ↦ g (Z ω, c)) (fun _ ↦ μ'') μ' := by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto hY

lemma TendstoInDistribution.add_of_tendstoInMeasure_const {X Y : ι → Ω'' → E}
    [l.IsCountablyGenerated] {c : E} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ ↦ c)) (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c) (fun _ ↦ μ'') μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) ↦ x.1 + x.2) (by fun_prop) hY_tendsto hY

end MeasureTheory
