/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Sub-Gaussian random variables

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details


TODO: this def forces the mean to be 0.
-/

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} (m : MeasurableSpace Ω) {m1 m2 mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
  {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0} {ε : ℝ}

lemma toReal_prob_le_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {s : Set Ω} :
    (μ s).toReal ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

lemma continuous_mgf (h : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Continuous (fun t ↦ mgf X μ t) := by
  rw [continuous_iff_continuousOn_univ]
  convert continuousOn_mgf
  ext t
  simp only [Set.mem_univ, true_iff]
  rw [mem_interior]
  refine ⟨Set.Ioo (t - 1) (t + 1), fun x hx ↦ ?_, isOpen_Ioo, by simp⟩
  exact integrable_exp_mul_of_le_of_le (h (t - 1)) (h (t + 1)) hx.1.le hx.2.le

lemma Memℒp.integrable_mul {Y : Ω → ℝ} (hX : Memℒp X 2 μ) (hY : Memℒp Y 2 μ) :
    Integrable (X * Y) μ := by
  have h := L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)
  simp only [RCLike.inner_apply, conj_trivial] at h
  have h_eq : X * Y =ᵐ[μ] fun ω ↦ hX.toLp X ω * hY.toLp Y ω := by
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hX hY
    simp [hX, hY]
  rwa [integrable_congr h_eq]

section Kernel

lemma _root_.MeasureTheory.Measure.integrable_compProd_snd_iff
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
    {μ : Measure α} {κ : Kernel α β}
    [SFinite μ] [IsSFiniteKernel κ] {f : β → E}
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable (fun p ↦ f p.2) (μ ⊗ₘ κ) ↔ Integrable f (κ ∘ₘ μ) := by
  have : κ ∘ₘ μ = (μ ⊗ₘ κ).map Prod.snd := by rw [← Measure.snd]; simp
  rw [this, integrable_map_measure _ measurable_snd.aemeasurable]
  · rfl
  · rwa [← this]

lemma ae_ae_of_ae_comp [SFinite ν] [IsSFiniteKernel κ]
    {p : Ω → Prop} (h : ∀ᵐ ω ∂(κ ∘ₘ ν), p ω):
    ∀ᵐ ω' ∂ν, ∀ᵐ ω ∂(κ ω'), p ω := by
  have : κ ∘ₘ ν = (ν ⊗ₘ κ).map Prod.snd := by rw [← Measure.snd]; simp
  simp_rw [this] at h
  exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map measurable_snd.aemeasurable h)

lemma todo_of_integrable_comp [SFinite ν] [IsSFiniteKernel κ] (h_int : Integrable X (κ ∘ₘ ν)) :
    (∀ᵐ x ∂ν, Integrable X (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖X y‖ ∂κ x) ν := by
  rw [← Measure.integrable_compProd_snd_iff h_int.1, Measure.integrable_compProd_iff h_int.1]
    at h_int
  exact h_int

lemma ae_integrable_of_integrable_comp [SFinite ν] [IsSFiniteKernel κ]
    (h_int : Integrable X (κ ∘ₘ ν)) :
    ∀ᵐ x ∂ν, Integrable X (κ x) := (todo_of_integrable_comp h_int).1

/-- A random variable is sub-Gaussian with parameter `c` with respect to a kernel `κ` and
a measure `μ` if `μ`-almost surely, for all `t : ℝ`, the moment generating function of `X`
with respect to `κ` is bounded by `exp (c * t ^ 2 / 2)`. -/
structure Kernel.IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t : ℝ, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

def Kernel.IsSubGaussian (X : Ω → ℝ) (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, Kernel.IsSubGaussianWith X c κ ν

namespace Kernel.IsSubGaussianWith

lemma aestronglyMeasurable (h : IsSubGaussianWith X c κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul 1
  simp only [one_mul] at h_int
  exact (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_integrable_exp_mul [SFinite ν] [IsSFiniteKernel κ]
    (h : IsSubGaussianWith X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ rexp (t * X y)) (κ ω') :=
  ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_aestronglyMeasurable [SFinite ν] [IsSFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  have h_int := h.ae_integrable_exp_mul 1
  simp only [one_mul] at h_int
  filter_upwards [h_int] with ω h_int
  exact (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_forall_integrable_exp_mul [SFinite ν] [IsSFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    fun _ ↦ h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

lemma integrableExpSet_eq_univ [SFinite ν] [IsSFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, integrableExpSet X (κ ω') = Set.univ := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' h_int
  ext t
  simp [h_int t, integrableExpSet]

lemma integrable_exp_mul_of_int
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω')) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  refine integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

protected lemma of_rat [SFinite ν] [IsSFiniteKernel κ]
    (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.IsSubGaussianWith X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
      refine integrable_exp_mul_of_int (fun n ↦ ?_)
      exact ae_integrable_of_integrable_comp (h_int n)
    filter_upwards [h_mgf, h_int]
      with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    refine isClosed_le ?_ (by fun_prop)
    refine continuous_mgf fun u ↦ ?_
    exact h_int _

lemma memℒp (h : IsSubGaussianWith X c κ ν) (t : ℝ) (p : ℝ≥0) :
    Memℒp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simp only [hp0, ENNReal.coe_zero, memℒp_zero_iff_aestronglyMeasurable]
    exact (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
    rotate_left
    · exact mod_cast hp0
    · simp
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert h' using 3 with p
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity)]
    swap; · simp
    rw [← exp_mul, mul_comm, ← mul_assoc]

lemma cgf_le [SFinite ν] [IsSFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simp only [h0, mgf_zero_measure, Pi.zero_apply, log_zero, log_exp]
      positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ ≤ c * t ^ 2 / 2 := by rw [log_exp]

@[simp]
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : IsSubGaussianWith (fun _ ↦ 0) 0 κ ν := by
  refine .of_rat ?_ ?_
  · simp
  · refine fun q ↦ ?_
    simp only [mgf_const', mul_zero, exp_zero, mul_one, NNReal.coe_zero, zero_mul, zero_div]
    exact ae_of_all _ fun _ ↦ toReal_prob_le_one

@[simp]
lemma zero' [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : IsSubGaussianWith 0 0 κ ν := zero

lemma congr [SFinite ν] [IsSFiniteKernel κ] {Y : Ω → ℝ} (h : IsSubGaussianWith X c κ ν)
    (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    IsSubGaussianWith Y c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω' hω'
    rw [hω']
  mgf_le := by
    have h'' := ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

lemma _root_.ProbabilityTheory.Kernel.isSubGaussianWith_congr [SFinite ν] [IsSFiniteKernel κ]
    {Y : Ω → ℝ} (h : X =ᵐ[κ ∘ₘ ν] Y) :
    IsSubGaussianWith X c κ ν ↔ IsSubGaussianWith Y c κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY <| by filter_upwards [h] with ω' hω' using hω'.symm⟩

lemma id_map (hX : Measurable X) :
    IsSubGaussianWith id c (κ.map X) ν ↔ IsSubGaussianWith X c κ ν := by
  have h_map : (κ.map X) ∘ₘ ν = (κ ∘ₘ ν).map X := by
    rw [← deterministic_comp_eq_map hX, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · intro t
    specialize h1 t
    rw [h_map] at h1
    rw [integrable_map_measure] at h1
    · exact h1
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h2
  · intro t
    specialize h1 t
    rw [h_map, integrable_map_measure]
    · exact h1
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h2

lemma measure_ge_le_exp_add [SFinite ν] [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t →
      ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h1 h2 t ht
  calc ((κ ω') {ω | ε ≤ X ω}).toReal
  _ ≤ exp (-t * ε) * mgf X (κ ω') t :=
    measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [SFinite ν] [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc ((κ ω') {ω | ε ≤ X ω}).toReal
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (- (ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by
    congr
    field_simp
    ring

lemma prob_ge_le [SFinite ν] [IsMarkovKernel κ] (h : IsSubGaussianWith X c κ ν) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · refine ae_of_all _ fun ω' ↦ ?_
    simpa [hc0] using toReal_prob_le_one
  · exact h.measure_ge_le (lt_of_le_of_ne zero_le' (Ne.symm hc0)) hε

section Indep

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} [SFinite ν] [IsSFiniteKernel κ]
    (hX : IsSubGaussianWith X cX κ ν) (hY : IsSubGaussianWith Y cY κ ν)
    (hindep : IndepFun X Y κ ν) :
    IsSubGaussianWith (X + Y) (cX + cY) κ ν := by
  have h_expX (t : ℝ) : ∃ X', StronglyMeasurable X'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * X ω)) =ᶠ[ae (κ ω')] X' := by
    obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * X' ω), continuous_exp.comp_stronglyMeasurable (hX'.const_mul _), ?_⟩
    filter_upwards [ae_ae_of_ae_comp hXX'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  have h_expY (t : ℝ) : ∃ Y', StronglyMeasurable Y'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * Y ω)) =ᶠ[ae (κ ω')] Y' := by
    obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * Y' ω), continuous_exp.comp_stronglyMeasurable (hY'.const_mul _), ?_⟩
    filter_upwards [ae_ae_of_ae_comp hYY'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  refine .of_rat ?_ ?_
  · intro t
    simp_rw [Pi.add_apply, mul_add, exp_add]
    exact Memℒp.integrable_mul (hX.memℒp t 2) (hY.memℒp t 2)
  · intro q
    have h := hindep.mgf_add (h_expX q) (h_expY q)
    filter_upwards [h, hX.mgf_le, hY.mgf_le] with ω' h hX hY
    calc mgf (X + Y) (κ ω') q
    _ = mgf X (κ ω') q * mgf Y (κ ω') q := by rw [h]
    _ ≤ exp (cX * q ^ 2 / 2) * exp (cY * q ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX q
      · exact hY q
    _ = exp ((cX + cY) * q ^ 2 / 2) := by
      rw [← exp_add]
      congr
      ring

lemma sum_of_iIndepFun {ι : Type*} [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ]
    {X : ι → Ω → ℝ} (h_indep : iIndepFun (fun _ ↦ inferInstance) X κ ν) {c : ι → ℝ≥0}
    (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_subG : ∀ i ∈ s, IsSubGaussianWith (X i) (c i) κ ν) :
    IsSubGaussianWith (∑ i ∈ s, X i) (∑ i ∈ s, c i) κ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his h =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    have h_indep' := (h_indep.indepFun_finset_sum_of_not_mem h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) h_indep'
    exact fun i hi ↦ h_subG _ (Finset.mem_insert_of_mem hi)

end Indep

end Kernel.IsSubGaussianWith

end Kernel

section Conditional

variable [StandardBorelSpace Ω] [IsFiniteMeasure μ]

def IsCondSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IsSubGaussianWith X c (condExpKernel μ m) (μ.trim hm)
  --integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  --mgf_le : ∀ᵐ ω' ∂(μ.trim hm), ∀ t : ℝ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2)

def IsCondSubGaussian (X : Ω → ℝ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  ∃ c : ℝ≥0, IsCondSubGaussianWith m hm X c μ

-- todo: fix measurable space arguments in Measure.bind and in Measure.snd_map_prod_mk
lemma condExpKernel_comp_trim : @Measure.bind _ _ m mΩ (μ.trim hm) (condExpKernel μ m) = μ := by
  rw [← Measure.snd_compProd, compProd_trim_condExpKernel, @Measure.snd_map_prod_mk]
  · simp
  · exact measurable_id'' hm

theorem condExp_ae_eq_trim_integral_condExpKernel {F : Type*} [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf : StronglyMeasurable f)
    (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω := by
 refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
 · exact stronglyMeasurable_condExp
 · exact hf.integral_condExpKernel
 · exact condExp_ae_eq_integral_condExpKernel hm hf_int

lemma IsCondSubGaussianWith.condExp_le (h : IsCondSubGaussianWith m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [ae_of_ae_trim hm h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

-- lemma isCondSubGaussianWith_iff_kernel (hX : Measurable X) [SFinite (μ.trim hm)] :
--   IsCondSubGaussianWith m hm X c μ
--     ↔ Kernel.IsSubGaussianWith X c (condExpKernel μ m) (μ.trim hm) := by
--   refine ⟨fun ⟨h1, h2⟩ ↦ .of_rat ?_ ?_, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
--   · rwa [condExpKernel_comp_trim]
--   · intro q
--     have h := condExp_ae_eq_trim_integral_condExpKernel' m hm ?_
--       (f := fun ω ↦ exp (q * X ω)) (μ := μ) ?_
--     rotate_left
--     · exact Measurable.stronglyMeasurable <| by fun_prop
--     · exact h1 q
--     filter_upwards [h2, h] with ω h2 h
--     specialize h2 q
--     rw [h] at h2
--     exact h2
--   · rwa [condExpKernel_comp_trim] at h1
--   · sorry

@[simp]
lemma IsCondSubGaussianWith.zero : IsCondSubGaussianWith m hm (fun _ ↦ 0) 0 μ :=
  Kernel.IsSubGaussianWith.zero

@[simp]
lemma IsCondSubGaussianWith.zero' : IsCondSubGaussianWith m hm 0 0 μ :=
  Kernel.IsSubGaussianWith.zero'

lemma IsCondSubGaussianWith.memℒp (h : IsCondSubGaussianWith m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    Memℒp (fun ω ↦ exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) m hm ▸ Kernel.IsSubGaussianWith.memℒp h t p

lemma IsCondSubGaussianWith.integrable_exp_mul (h : IsCondSubGaussianWith m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) m hm ▸ Kernel.IsSubGaussianWith.integrable_exp_mul h t

end Conditional

structure IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

def IsSubGaussian (X : Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, IsSubGaussianWith X c μ

lemma isSubGaussianWith_iff_kernel :
  IsSubGaussianWith X c μ
    ↔ Kernel.IsSubGaussianWith X c (Kernel.const Unit μ) (Measure.dirac ()) := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa
  · simpa
  · simpa using h1
  · simpa using h2

lemma isSubGaussian_iff_kernel :
  IsSubGaussian X μ ↔ Kernel.IsSubGaussian X (Kernel.const Unit μ) (Measure.dirac ()) := by
  simp_rw [IsSubGaussian, Kernel.IsSubGaussian, isSubGaussianWith_iff_kernel]

namespace IsSubGaussianWith

lemma memℒp (h : IsSubGaussianWith X c μ) (t : ℝ) (p : ℝ≥0) :
    Memℒp (fun ω ↦ exp (t * X ω)) p μ := by
  rw [isSubGaussianWith_iff_kernel] at h
  have hp := h.memℒp t p
  simpa using hp

lemma cgf_le [SFinite μ] (h : IsSubGaussianWith X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.cgf_le t

@[simp]
lemma zero [IsZeroOrProbabilityMeasure μ] : IsSubGaussianWith (fun _ ↦ 0) 0 μ := by
  simp [isSubGaussianWith_iff_kernel]

@[simp]
lemma zero' [IsZeroOrProbabilityMeasure μ] : IsSubGaussianWith 0 0 μ := by
  simp [isSubGaussianWith_iff_kernel]

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteMeasure μ] (h : IsSubGaussianWith X c μ) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.measure_ge_le hc hε

lemma prob_ge_le [IsProbabilityMeasure μ] (h : IsSubGaussianWith X c μ) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.prob_ge_le hε

lemma add_of_indepFun [SFinite μ] {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : IsSubGaussianWith X cX μ)
    (hY : IsSubGaussianWith Y cY μ) (hindep : IndepFun X Y μ) :
    IsSubGaussianWith (X + Y) (cX + cY) μ := by
  rw [isSubGaussianWith_iff_kernel] at hX hY ⊢
  simpa using hX.add_of_indepFun hY hindep

end IsSubGaussianWith

section Martingale

lemma isSubGaussianWith_add_of_isCondSubGaussianWith [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {cY : ℝ≥0} (hm : m ≤ mΩ) (hXm : Measurable[m] X)
    (hX : IsSubGaussianWith X c μ) (hY : IsCondSubGaussianWith m hm Y cY μ) :
    IsSubGaussianWith (X + Y) (c + cY) μ where
  integrable_exp_mul t := by
    simp_rw [Pi.add_apply, mul_add, exp_add]
    exact Memℒp.integrable_mul (hX.memℒp t 2) (hY.memℒp m hm t 2)
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = ∫ ω, exp (t * X ω) * exp (t * Y ω) ∂μ := by
      simp only [mgf, Pi.add_apply, mul_add, exp_add]
    _ = ∫ ω, (μ[fun ω ↦ exp (t * X ω) * exp (t * Y ω) | m]) ω ∂μ := by rw [integral_condExp hm]
    _ = ∫ ω, exp (t * X ω) * (μ[fun ω ↦ exp (t * Y ω) | m]) ω ∂μ := by
      refine integral_congr_ae ?_
      refine condExp_mul_of_aestronglyMeasurable_left ?_ ?_ (hY.integrable_exp_mul m hm t)
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · exact Memℒp.integrable_mul (hX.memℒp t 2) (hY.memℒp m hm t 2)
    _ ≤ ∫ ω, exp (t * X ω) * exp (cY * t^2 / 2) ∂μ := by
      refine integral_mono_of_nonneg ?_ ((hX.integrable_exp_mul t).mul_const _) ?_
      · have h := condExp_mono (f := 0) (g := fun ω ↦ exp (t * Y ω)) (μ := μ) (m := m)
          (integrable_const 0) (hY.integrable_exp_mul m hm t) (ae_of_all _ fun ω ↦ by positivity)
        simp only [condExp_zero] at h
        filter_upwards [h] with ω hω
        refine mul_nonneg (by positivity) hω
      · filter_upwards [hY.condExp_le m hm t] with ω hω
        gcongr
    _ = mgf X μ t * exp (cY * t^2 / 2) := by rw [integral_mul_right, mgf]
    _ ≤ exp (c * t^2 / 2) * exp (cY * t^2 / 2) := by
      gcongr
      exact hX.mgf_le t
    _ = exp ((c + cY) * t ^ 2 / 2) := by
      rw [← exp_add]
      congr
      ring

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ} [IsFiniteMeasure μ]

-- In particular, `∑ i, Y i` is a martingale.
lemma isSubGaussianWith_sum_of_isCondSubGaussianWith [StandardBorelSpace Ω]
    [IsZeroOrProbabilityMeasure μ] (h_adapted : Adapted ℱ Y)
    (h_subG : ∀ i, IsCondSubGaussianWith (ℱ i) (ℱ.le i) (Y i) (cY i) μ) (n : ℕ) :
    IsSubGaussianWith (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_rw [Finset.sum_range_succ]
    refine isSubGaussianWith_add_of_isCondSubGaussianWith (ℱ n) (ℱ.le n) ?_ hn (h_subG n)
    exact Finset.measurable_sum (Finset.range n) fun m hm ↦
      ((h_adapted m).mono (ℱ.mono (Finset.mem_range_le hm))).measurable

end Martingale

end ProbabilityTheory
