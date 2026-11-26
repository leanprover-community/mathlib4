/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.SetToL1.Function

/-!
# Convergence and measurability for set-to-function extensions

This file proves norm estimates and dominated-convergence results for `MeasureTheory.setToFun`.
It includes sequential and filter versions of dominated convergence, applications to infinite
sums, strong measurability for parameterized families, and continuity results for families
dominated by an integrable function.
-/

@[expose] public section

noncomputable section

open scoped Topology

open Set Filter TopologicalSpace ENNReal

namespace MeasureTheory

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

section Function

variable {T : Set α → E →L[ℝ] F} {C : ℝ} {f : α → E}

theorem norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E)
    (hC : 0 ≤ C) : ‖setToFun μ T hT f‖ ≤ C * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm hT hC f

theorem norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm' hT f

theorem norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ C * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm hT hC _

theorem norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm' hT _

theorem enorm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ₑ ≤ NNReal.mk C hC * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ; swap
  · simp [setToFun_undef _ hf]
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne)).1
  simp only [toReal_enorm, toReal_mul, coe_toReal, NNReal.coe_mk]
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  apply le_of_eq
  rw [Integrable.norm_toL1_eq_lintegral_enorm]

theorem norm_setToFun_le_toReal (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ NNReal.mk C hC * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  by_cases hf : Integrable f μ; swap
  · simp only [setToFun_undef _ hf, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  · simp
  rw [Integrable.norm_toL1_eq_lintegral_enorm]
  simp

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `setToFun`.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {fs : ℕ → α → E} {f : α → E} (bound : α → ℝ)
    (fs_measurable : ∀ n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) atTop (𝓝 <| setToFun μ T hT f) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consider are integrable
  have fs_int : ∀ n, Integrable (fs n) μ := fun n =>
    bound_integrable.mono' (fs_measurable n) (h_bound _)
  have f_int : Integrable f μ :=
    ⟨f_measurable,
      hasFiniteIntegral_of_dominated_convergence bound_integrable.hasFiniteIntegral h_bound
        h_lim⟩
  -- it suffices to prove the result for the corresponding L1 functions
  suffices
    Tendsto (fun n => L1.setToL1 hT ((fs_int n).toL1 (fs n))) atTop
      (𝓝 (L1.setToL1 hT (f_int.toL1 f))) by
    convert! this with n
    · exact setToFun_eq hT (fs_int n)
    · exact setToFun_eq hT f_int
  -- the convergence of setToL1 follows from the convergence of the L1 functions
  refine L1.tendsto_setToL1 hT _ _ ?_
  -- up to some rewriting, what we need to prove is `h_lim`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have lintegral_norm_tendsto_zero :
    Tendsto (fun n => ENNReal.toReal <| ∫⁻ a, ENNReal.ofReal ‖fs n a - f a‖ ∂μ) atTop (𝓝 0) :=
    (tendsto_toReal zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence fs_measurable
        bound_integrable.hasFiniteIntegral h_bound h_lim)
  convert! lintegral_norm_tendsto_zero with n
  rw [L1.norm_def]
  congr 1
  refine lintegral_congr_ae ?_
  rw [← Integrable.toL1_sub]
  refine ((fs_int n).sub f_int).coeFn_toL1.mono fun x hx => ?_
  dsimp only
  rw [hx, ofReal_norm, Pi.sub_apply]

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι}
    {l : Filter ι} [l.IsCountablyGenerated] {fs : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hfs_meas : ∀ᶠ n in l, AEStronglyMeasurable (fs n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) l (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT f) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : ∀ s ∈ l, ∃ a, ∀ b ≥ a, x b ∈ s := by rwa [tendsto_atTop'] at xl
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } ∩
        { x : ι | (fun n => ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) x } ∈ l :=
    inter_mem hfs_meas h_bound
  obtain ⟨k, h⟩ := hxl _ h
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_setToFun_of_dominated_convergence hT bound ?_ bound_integrable ?_ ?_
  · exact fun n => (h _ (self_le_add_left _ _)).1
  · exact fun n => (h _ (self_le_add_left _ _)).2
  · filter_upwards [h_lim]
    refine fun a h_lin => @Tendsto.comp _ _ _ (fun n => x (n + k)) (fun n => fs n a) _ _ _ h_lin ?_
    rwa [tendsto_add_atTop_iff_nat]

/-- Lebesgue dominated convergence theorem for series. -/
theorem hasSum_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {F : ι → α → E} {f : α → E}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => setToFun μ T hT (F n)) (setToFun μ T hT f) := by
  have hb_nonneg : ∀ᵐ a ∂μ, ∀ n, 0 ≤ bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : ∀ n, bound n ≤ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using ha_sum.le_tsum _ fun i _ => ha0 i
  have hF_integrable : ∀ n, Integrable (F n) μ := by
    refine fun n => bound_integrable.mono' (hF_meas n) ?_
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← setToFun_finsetSum _ _ fun n _ => hF_integrable n]
  refine tendsto_setToFun_filter_of_dominated_convergence _
      (fun a => ∑' n, bound n a) ?_ ?_ bound_integrable h_lim
  · exact Eventually.of_forall fun s => s.aestronglyMeasurable_fun_sum fun n _ => hF_meas n
  · filter_upwards with s
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n ∈ s, F n a‖ ≤ ∑ n ∈ s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ ≤ ∑' n, bound n a := has.sum_le_tsum _ (fun n _ => ha0 n)

theorem setToFun_tsum [CompleteSpace E] (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ ≠ ∞) :
    setToFun μ T hT (fun a ↦ ∑' i, f i a) = ∑' i, setToFun μ T hT (f i) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : ∀ᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert!
    (MeasureTheory.hasSum_setToFun_of_dominated_convergence hT (fun i a => ‖f i a‖₊) hf _ hhh ⟨_, _⟩
        _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · fun_prop
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert! this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum

/-- Corollary of the Lebesgue dominated convergence theorem: If a sequence of functions `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwise to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` converge
to the integral of `f`. -/
theorem tendsto_setToFun_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ T C)
    {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → E} [IsFiniteMeasure μ] {f : α → E}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C, ∀ᶠ n in l, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => setToFun μ T hT (F n)) l (𝓝 (setToFun μ T hT f)) := by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α → ℝ := (fun _ => c)
  exact tendsto_setToFun_filter_of_dominated_convergence hT
    C h_meas h_boundc (integrable_const c) h_lim

omit [NormedSpace ℝ E] in
theorem _root_.measurableSet_integrable {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    MeasurableSet {x | Integrable (f x) μ} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. This version has `f` in curried form. -/
theorem StronglyMeasurable.setToFun_prod_right {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (β × α)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun x => setToFun μ T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  have : SeparableSpace (range (Function.uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (β × α) E :=
    SimpleFunc.approxOn _ hf.measurable (range (Function.uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → β → SimpleFunc α E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : ℕ → β → F := fun n =>
    {x | Integrable (f x) μ}.indicator fun x => (s' n x).setToSimpleFunc T
  have hf' n : StronglyMeasurable (f' n) := by
    refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have : ∀ x, ((s' n x).range.filter fun x => x ≠ 0) ⊆ (s n).range := by
      intro x; refine Finset.Subset.trans (Finset.filter_subset _ _) ?_; intro y
      simp_rw [SimpleFunc.mem_range]; rintro ⟨z, rfl⟩; exact ⟨(x, z), rfl⟩
    simp_rw [SimpleFunc.setToSimpleFunc_eq_sum_of_subset T hT.1.map_empty_eq_zero (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply StronglyMeasurable.apply_continuousLinearMap
    apply h'T
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : β => setToFun μ T hT (f x)) := by
    apply tendsto_pi_nhds.2 fun x ↦ ?_
    by_cases hfx : Integrable (f x) μ
    · have (n : _) : Integrable (s' n x) μ := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [mem_ofPred_eq, hfx, indicator_of_mem, this,
        ← setToFun_simpleFunc_eq_setToSimpleFunc hT, f']
      refine
        tendsto_setToFun_of_dominated_convergence hT (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · refine fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le ?_ ?_ (x, y) n
        · exact hf.measurable
        · simp
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn ?_ ?_ ?_
        · exact hf.measurable.of_uncurry_left
        · simp
        apply subset_closure
        simp [-Function.uncurry_apply_pair]
    · simp [f', hfx, setToFun_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C)
    {fs : X → α → E} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hfs_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => fs x a) s x₀) :
    ContinuousWithinAt (fun x => setToFun μ T hT (fs x)) s x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

theorem continuousAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {x₀ : X} {bound : α → ℝ} (hfs_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => fs x a) x₀) :
    ContinuousAt (fun x => setToFun μ T hT (fs x)) x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

theorem continuousOn_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} {s : Set X} (hfs_meas : ∀ x ∈ s, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => fs x a) s) :
    ContinuousOn (fun x => setToFun μ T hT (fs x)) s := by
  intro x hx
  refine continuousWithinAt_setToFun_of_dominated hT ?_ ?_ bound_integrable ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
  · filter_upwards [h_cont] with a ha using ha x hx

theorem continuous_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} (hfs_meas : ∀ x, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, Continuous fun x => fs x a) : Continuous fun x => setToFun μ T hT (fs x) :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_setToFun_of_dominated hT (Eventually.of_forall hfs_meas)
        (Eventually.of_forall h_bound) ‹_› <|
      h_cont.mono fun _ => Continuous.continuousAt

end Function

end MeasureTheory
