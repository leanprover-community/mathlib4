import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Outline of portmanteau implication: liminf condition for open sets implies weak convergence

This file contains steps needed to prove the portmanteau implication
`le_liminf_open_implies_convergence`. Some intermediate steps need to be generalized
and cleaned up, and are to be placed in appropriate files. The main part should go
to the file `Mathlib.MeasureTheory.Measure.Portmanteau`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

noncomputable def ENNReal.truncateToReal (t x : ℝ≥0∞) : ℝ :=
  (min t x).toReal

lemma ENNReal.truncateToReal_eq_toReal {t x : ℝ≥0∞} (t_ne_top : t ≠ ∞) (x_le : x ≤ t) :
    ENNReal.truncateToReal t x = x.toReal := by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x ≠ ∞ := by
    simp_all only [ne_eq, ge_iff_le, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal obs x_lt_top.ne).mpr (min_eq_right x_le)

lemma ENNReal.truncateToReal_le {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) {x : ℝ≥0∞} :
    ENNReal.truncateToReal t x ≤ t.toReal := by
  rw [ENNReal.truncateToReal]
  apply (toReal_le_toReal _ t_ne_top).mpr (min_le_left t x)
  simp_all only [ne_eq, ge_iff_le, min_eq_top, false_and, not_false_eq_true]

lemma ENNReal.truncateToReal_nonneg {t x : ℝ≥0∞} :
    0 ≤ ENNReal.truncateToReal t x := toReal_nonneg

lemma ENNReal.monotone_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) :
    Monotone (ENNReal.truncateToReal t) := by
  intro x y x_le_y
  have obs_x : min t x ≠ ∞ := by
    simp_all only [ne_eq, ge_iff_le, min_eq_top, false_and, not_false_eq_true]
  have obs_y : min t y ≠ ∞ := by
    simp_all only [ne_eq, ge_iff_le, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_le_toReal obs_x obs_y).mpr (min_le_min_left t x_le_y)

-- Q: Missing?
lemma ENNReal.continuousOn_toReal :
    ContinuousOn (fun (x : ℝ≥0∞) ↦ x.toReal) { x | x ≠ ∞ } := by
  change ContinuousOn (((↑) : ℝ≥0 → ℝ) ∘ (fun (x : ℝ≥0∞) ↦ x.toNNReal)) { x | x ≠ ∞ }
  apply NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

lemma ENNReal.continuous_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) :
    Continuous (ENNReal.truncateToReal t) := by
  apply ENNReal.continuousOn_toReal.comp_continuous (continuous_min.comp (Continuous.Prod.mk t))
  simp [t_ne_top]

lemma bar {ι : Type*} {F : Filter ι} [NeBot F]  {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) {xs : ι → ℝ≥0∞}
  (le_b : ∀ i, xs i ≤ b) :
    F.liminf (fun i ↦ (xs i).toReal) = (F.liminf xs).toReal := by
  have liminf_le : F.liminf xs ≤ b := by
    apply liminf_le_of_le
    · use 0
      simp only [ge_iff_le, zero_le, eventually_map, eventually_true]
    · intro y h
      obtain ⟨i, hi⟩ := h.exists
      exact hi.trans (le_b i)
  have key : ∀ i, (xs i).toReal = ENNReal.truncateToReal b (xs i) := by
    intro i
    rw [ENNReal.truncateToReal_eq_toReal b_ne_top (le_b i)]
  have key' : (F.liminf xs).toReal = ENNReal.truncateToReal b (F.liminf xs) := by
    rw [ENNReal.truncateToReal_eq_toReal b_ne_top liminf_le]
  simp_rw [key, key']
  have := @Monotone.map_liminf_of_continuousAt ι ℝ≥0∞ ℝ F _ _ _ _ _ _ _ _
          (ENNReal.monotone_truncateToReal b_ne_top) xs
          (ENNReal.continuous_truncateToReal b_ne_top).continuousAt ?_ ?_
  · rw [this]
    rfl
  · use b
    simp only [eventually_map]
    exact eventually_of_forall le_b
  · use 0
    apply eventually_of_forall
    intro y
    simp only [ge_iff_le, zero_le]

-- NOTE: Missing from Mathlib?
-- What would be a good generality?
-- (Mixes order-boundedness and metric-boundedness, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  refine isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩

lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩


section le_liminf_open_implies_convergence

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

-- NOTE: I think I will work with real-valued integrals, after all...
lemma fatou_argument_lintegral
    {μ : Measure Ω} [SigmaFinite μ] {μs : ℕ → Measure Ω} [∀ i, SigmaFinite (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall f_nn) f_cont.aemeasurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a})
            := (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans ?_
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a})
            := lintegral_liminf_le (fun n ↦ Antitone.measurable
                (fun s t hst ↦ measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
  rfl

theorem BoundedContinuousFunction.lintegral_le_edist_mul
  {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ≥0) :
    (∫⁻ x, f x ∂μ) ≤ edist 0 f * (μ Set.univ) := by
  have bound : ∀ x, f x ≤ nndist 0 f := by
    intro x
    convert nndist_coe_le_nndist x
    simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]
  apply le_trans (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.mpr (bound x)))
  simp

lemma ENNReal.monotoneOn_toReal : MonotoneOn ENNReal.toReal {∞}ᶜ :=
  fun _ _ _ hy x_le_y ↦ toReal_mono hy x_le_y

-- Argh. :|
lemma Real.lipschitzWith_toNNReal : LipschitzWith 1 Real.toNNReal := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, NNReal.dist_eq, coe_toNNReal', ge_iff_le, Real.dist_eq]
  simpa only [ge_iff_le, NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

-- NOTE: I think this is the version I prefer to use, after all...
lemma fatou_argument_integral_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  have earlier := fatou_argument_lintegral f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (eventually_of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert (ENNReal.toReal_le_toReal ?_ ?_).mpr earlier
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (eventually_of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    let c := nndist 0 g
    have c_ne_top : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ c := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    have obs₁ := fun i ↦ @ENNReal.truncateToReal_eq_toReal c _ c_ne_top (bound i)
    simp only [← obs₁]
    have := @Monotone.map_liminf_of_continuousAt ℕ ℝ≥0∞ ℝ atTop _ _ _ _ _ _ _
            (ENNReal.truncateToReal c) (ENNReal.monotone_truncateToReal (t := c) c_ne_top)
            (fun i ↦ ∫⁻ (a : Ω), ENNReal.ofReal (f a) ∂μs i)
            (ENNReal.continuous_truncateToReal (t := c) c_ne_top).continuousAt ?_ ?_
    · convert this.symm using 1
      apply (ENNReal.truncateToReal_eq_toReal c_ne_top _).symm
      apply liminf_le_of_le ?_ (fun b h ↦ ?_)
      · use 0
        simp only [ge_iff_le, zero_le, eventually_map, eventually_atTop, implies_true, forall_const,
          exists_const]
      obtain ⟨i, hi⟩ := h.exists
      exact hi.trans (bound i)
    · use c
      simp only [coe_nnreal_ennreal_nndist, eventually_map, eventually_atTop, ge_iff_le]
      use 0
      exact fun j _ ↦  bound j
    · use 0
      simp only [ge_iff_le, zero_le, eventually_map, eventually_atTop, implies_true, forall_const,
        exists_const]
  · exact (f.lintegral_of_real_lt_top μ).ne
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp at obs
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

lemma reduction_to_liminf {ι : Type*} {L : Filter ι} [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_le_map_of_bounded_range _ obs
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_ge_map_of_bounded_range _ obs
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, (f x) ∂ (μs i)) (∫ x, (f x) ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    -- TODO: Should the case of ⊥ filter be treated separately and not included as an assumption?
    have := liminf_add_const L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

-- Not needed?
/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
lemma ProbabilityMeasure.tendsto_iff_forall_nonneg_integral_tendsto {γ : Type _} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ, 0 ≤ f →
        Tendsto (fun i ↦ ∫ ω, (f ω) ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, (f ω) ∂(μ : Measure Ω))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f _ ↦ h f, fun h f ↦ ?_⟩
  set g := f + BoundedContinuousFunction.const _ ‖f‖ with g_def
  have fx_eq : ∀ x, f x = g x - ‖f‖ := by
    intro x
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_toFun, Pi.add_apply,
               add_sub_cancel]
  have key := h g (f.add_norm_nonneg)
  simp [g_def] at key
  simp_rw [integral_add (f.integrable _) (integrable_const ‖f‖)] at key
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
  simp_rw [fx_eq]
  convert tendsto_add.comp (Tendsto.prod_mk_nhds key (@tendsto_const_nhds _ _ _ (-‖f‖) F)) <;> simp

theorem le_liminf_open_implies_convergence {μ : ProbabilityMeasure Ω}
  {μs : ℕ → ProbabilityMeasure Ω} (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  apply reduction_to_liminf
  intro f f_nn
  apply fatou_argument_integral_nonneg (f := f) f_nn
  intro G G_open
  specialize h_opens G G_open
  simp only at h_opens
  simp only [liminf, limsInf, eventually_map, eventually_atTop, ge_iff_le, le_sSup_iff] at *
  intro b b_ub
  by_cases b_eq_top : b = ∞
  · simp only [b_eq_top, le_top]
  · have foo := (@le_csSup_iff ℝ≥0 _ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → a ≤ ENNReal.toNNReal (μs b G)}
              (ENNReal.toNNReal (μ G)) ?_ ?_).mp h_opens (ENNReal.toNNReal b) ?_
    · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at foo
      convert ENNReal.coe_le_coe.mpr foo
      · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · simp only [ne_eq, b_eq_top, not_false_eq_true, ENNReal.coe_toNNReal]
    · use 1
      simp [mem_upperBounds]
      intro x n hn
      exact (hn n (le_refl n)).trans (ProbabilityMeasure.apply_le_one _ _)
    · refine ⟨0, by simp⟩
    · simp only [mem_upperBounds, Set.mem_setOf_eq, forall_exists_index, ne_eq,
                 ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at b_ub ⊢
      intro x n hn
      specialize b_ub x n ?_
      · intro m hm
        convert ENNReal.coe_le_coe.mpr (hn m hm)
        simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · rw [(ENNReal.coe_toNNReal b_eq_top).symm] at b_ub
        exact ENNReal.coe_le_coe.mp b_ub

end le_liminf_open_implies_convergence
