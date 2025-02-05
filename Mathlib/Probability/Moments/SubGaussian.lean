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

section Kernel

lemma todo' [SFinite ν] [IsSFiniteKernel κ] [Nonempty Ω']
    (h : AEStronglyMeasurable (fun p ↦ X p.2) (ν ⊗ₘ κ)) :
    ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X' := by
  unfold AEStronglyMeasurable Filter.EventuallyEq at h
  obtain ⟨g, hg, h_eq⟩ := h
  simp only at h_eq
  let ω'₀ : Ω' := Nonempty.some inferInstance
  refine ⟨fun ω ↦ g (ω'₀, ω), hg.comp_measurable measurable_prod_mk_left, ?_⟩
  --refine Measure.ae_ae_of_ae_compProd ?_
  --rw [Measure.ae_compProd_iff] at h_eq
  sorry

/-- A random variable is sub-Gaussian with parameter `c` with respect to a kernel `κ` and
a measure `μ` if `μ`-almost surely, for all `t : ℝ`, the moment generating function of `X`
with respect to `κ` is bounded by `exp (c * t ^ 2 / 2)`. -/
structure Kernel.IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  -- todo: this could be a consequence of `AEStronglyMeasurable (fun p ↦ X p.2) (ν ⊗ₘ κ)`?
  aestronglyMeasurable : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X'
  hasFiniteIntegral_exp_mul : ∀ᵐ ω' ∂ν, ∀ t : ℝ, HasFiniteIntegral (fun ω ↦ exp (t * X ω)) (κ ω')
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t : ℝ, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

def Kernel.IsSubGaussian (X : Ω → ℝ) (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, Kernel.IsSubGaussianWith X c κ ν

namespace Kernel.IsSubGaussianWith

lemma ae_aestronglyMeasurable (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  obtain ⟨X', hX', hXX'⟩ := h.aestronglyMeasurable
  filter_upwards [hXX'] with ω' h using ⟨X', hX', h⟩

lemma integrable_exp_mul (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  obtain ⟨X', hX', hXX'⟩ := h.aestronglyMeasurable
  filter_upwards [h.hasFiniteIntegral_exp_mul, hXX'] with ω' h_int hXX' t
  refine ⟨⟨fun ω ↦ exp (t * X' ω), ?_, ?_⟩, h_int t⟩
  · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
  · filter_upwards [hXX'] with ω hω
    rw [hω]

lemma integrableExpSet_eq_univ (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, integrableExpSet X (κ ω') = Set.univ := by
  filter_upwards [h.integrable_exp_mul] with ω' h_int
  ext t
  simp [h_int t, integrableExpSet]

lemma hasFiniteIntegral_exp_mul_of_int
    (h_meas : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, HasFiniteIntegral (fun ω ↦ exp (n * X ω)) (κ ω')) :
    ∀ᵐ ω' ∂ν, ∀ t, HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) (κ ω') := by
  rw [← ae_all_iff] at h_int
  obtain ⟨X', hX', hXX'⟩ := h_meas
  filter_upwards [h_int, hXX'] with ω' h_int hXX' t
  refine (integrable_exp_mul_of_le_of_le ?_ ?_ (Int.floor_le t) (Int.le_ceil t)).2
  · refine ⟨⟨fun ω ↦ exp (⌊t⌋ * X' ω), ?_, ?_⟩, h_int _⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]
  · refine ⟨⟨fun ω ↦ exp (⌈t⌉ * X' ω), ?_, ?_⟩, h_int _⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]

open Filter in
protected lemma of_rat (h_meas : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, HasFiniteIntegral (fun ω ↦ exp (n * X ω)) (κ ω'))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.IsSubGaussianWith X c κ ν where
  aestronglyMeasurable := h_meas
  hasFiniteIntegral_exp_mul := hasFiniteIntegral_exp_mul_of_int h_meas h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    let ⟨X', hX', hXX'⟩ := h_meas
    filter_upwards [h_mgf, hasFiniteIntegral_exp_mul_of_int h_meas h_int, hXX']
      with ω' h_mgf h_int hXX' t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    refine isClosed_le ?_ (by fun_prop)
    refine continuous_mgf fun u ↦ ?_
    refine ⟨⟨fun ω ↦ exp (u * X' ω), ?_, ?_⟩, h_int u⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]

lemma cgf_le (h : IsSubGaussianWith X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.integrable_exp_mul] with ω' h h_int
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
lemma zero [IsZeroOrMarkovKernel κ] : IsSubGaussianWith (fun _ ↦ 0) 0 κ ν := by
  refine .of_rat ?_ ?_ ?_
  · exact ⟨fun _ ↦ 0, stronglyMeasurable_const, by simp⟩
  · refine fun n ↦ ae_of_all _ fun ω ↦ ?_
    simp only [mul_zero, exp_zero]
    exact hasFiniteIntegral_const _
  · refine fun q ↦ ?_
    simp only [mgf_const', mul_zero, exp_zero, mul_one, NNReal.coe_zero, zero_mul, zero_div]
    exact ae_of_all _ fun _ ↦ toReal_prob_le_one

@[simp]
lemma zero' [IsZeroOrMarkovKernel κ] : IsSubGaussianWith 0 0 κ ν := zero

lemma congr {Y : Ω → ℝ} (h : IsSubGaussianWith X c κ ν) (h' : ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] Y) :
    IsSubGaussianWith Y c κ ν where
  aestronglyMeasurable := by
    obtain ⟨X', hX', hXX'⟩ := h.aestronglyMeasurable
    refine ⟨X', hX', ?_⟩
    filter_upwards [hXX', h'] with ω hXX' h' using h'.symm.trans hXX'
  hasFiniteIntegral_exp_mul := by
    filter_upwards [h.hasFiniteIntegral_exp_mul, h'] with ω' h_int h' t
    refine (hasFiniteIntegral_congr ?_).mpr (h_int t)
    filter_upwards [h'] with ω hω
    rw [hω]
  mgf_le := by
    filter_upwards [h.mgf_le, h'] with ω' h_mgf h' t
    rw [mgf_congr h'.symm]
    exact h_mgf t

lemma _root_.ProbabilityTheory.Kernel.isSubGaussianWith_congr {Y : Ω → ℝ}
    (h : ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] Y) :
    IsSubGaussianWith X c κ ν ↔ IsSubGaussianWith Y c κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY <| by filter_upwards [h] with ω' hω' using hω'.symm⟩

lemma id_map (hX : Measurable X) :
    IsSubGaussianWith id c (κ.map X) ν ↔ IsSubGaussianWith X c κ ν := by
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · exact ⟨X, hX.stronglyMeasurable, by simp⟩
  · filter_upwards [h2] with ω' h2 t
    simp_rw [hasFiniteIntegral_def] at h2 ⊢
    convert h2 t
    rw [lintegral_map _ hX]
    · simp
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h3
  · exact ⟨id, stronglyMeasurable_id, by simp⟩
  · filter_upwards [h2] with ω' h2 t
    simp_rw [hasFiniteIntegral_def] at h2 ⊢
    convert h2 t
    rw [lintegral_map _ hX]
    · simp
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h3

lemma measure_ge_le_exp_add [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t →
      ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.integrable_exp_mul] with ω' h1 h2 t ht
  calc ((κ ω') {ω | ε ≤ X ω}).toReal
  _ ≤ exp (-t * ε) * mgf X (κ ω') t :=
    measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) {ε : ℝ}
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

lemma prob_ge_le [IsMarkovKernel κ] (h : IsSubGaussianWith X c κ ν) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · refine ae_of_all _ fun ω' ↦ ?_
    simpa [hc0] using toReal_prob_le_one
  · exact h.measure_ge_le (lt_of_le_of_ne zero_le' (Ne.symm hc0)) hε

section Indep

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : IsSubGaussianWith X cX κ ν)
    (hY : IsSubGaussianWith Y cY κ ν) (hindep : IndepFun X Y κ ν) :
    IsSubGaussianWith (X + Y) (cX + cY) κ ν := by
  obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
  obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
  have h_expX (t : ℝ) : ∃ X', StronglyMeasurable X'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * X ω)) =ᶠ[ae (κ ω')] X' := by
    obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * X' ω), continuous_exp.comp_stronglyMeasurable (hX'.const_mul _), ?_⟩
    filter_upwards [hXX'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  have h_expY (t : ℝ) : ∃ Y', StronglyMeasurable Y'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * Y ω)) =ᶠ[ae (κ ω')] Y' := by
    obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * Y' ω), continuous_exp.comp_stronglyMeasurable (hY'.const_mul _), ?_⟩
    filter_upwards [hYY'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  refine .of_rat ?_ ?_ ?_
  · refine ⟨X' + Y', hX'.add hY', ?_⟩
    filter_upwards [hXX', hYY'] with ω hX hY
    exact hX.add hY
  · intro n
    have h := hindep.integrable_exp_mul_add (h_expX n) (h_expY n)
    filter_upwards [h.2, hX.integrable_exp_mul, hY.integrable_exp_mul] with ω' h hX hY
    specialize h (hX n) (hY n)
    exact h.2
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

lemma sum_of_iIndepFun {ι : Type*} [IsZeroOrMarkovKernel κ]
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

def IsCondSubGaussian (X : Ω → ℝ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  ∃ c : ℝ≥0, IsCondSubGaussianWith m hm X c μ

@[simp]
lemma zero : IsCondSubGaussianWith m hm (fun _ ↦ 0) 0 μ := Kernel.IsSubGaussianWith.zero

@[simp]
lemma zero' : IsCondSubGaussianWith m hm 0 0 μ := Kernel.IsSubGaussianWith.zero'

section Martingale

lemma todo_add {Y : Ω → ℝ} {cY : ℝ≥0} (hm12 : m1 ≤ m2) (hm2 : m2 ≤ mΩ)
    (hXm : Measurable[m2] X) (hYm : Measurable[mΩ] Y)
    (hX : IsCondSubGaussianWith m1 (hm12.trans hm2) X c μ)
    (hY : IsCondSubGaussianWith m2 hm2 Y cY μ) :
    IsCondSubGaussianWith m2 hm2 (X + Y) (c + cY) μ := by
  refine .of_rat ?_ ?_ ?_
  · exact ⟨X + Y, (hXm.mono hm2 le_rfl).stronglyMeasurable.add hYm.stronglyMeasurable, by simp⟩
  · intro n
    suffices ∀ᵐ ω' ∂μ.trim hm2, Integrable (fun ω ↦ exp (n * (X + Y) ω)) (condExpKernel μ m2 ω') by
      filter_upwards [this] with ω' hω' using hω'.2
    have : μ.trim (hm12.trans hm2) = (μ.trim hm2).trim hm12 := trim_trim.symm
    have hX_int' := hX.integrable_exp_mul
    rw [this] at hX_int'
    have hX_int := ae_of_ae_trim hm12 hX_int'
    have hY_int := hY.integrable_exp_mul
    filter_upwards [hX_int, hY_int] with ω hX_int hY_int
    simp only [Pi.add_apply, NNReal.coe_add, mul_add, exp_add]
    sorry
  · intro t
    have : μ.trim (hm12.trans hm2) = (μ.trim hm2).trim hm12 := trim_trim.symm
    have hX_int' := hX.integrable_exp_mul
    have hX_mgf' := hX.mgf_le
    rw [this] at hX_mgf' hX_int'
    have hX_mgf := ae_of_ae_trim hm12 hX_mgf'
    have hY_mgf := hY.mgf_le
    have hX_int := ae_of_ae_trim hm12 hX_int'
    have hY_int := hY.integrable_exp_mul
    simp_rw [mgf]
    have h := condExp_ae_eq_integral_condExpKernel hm2 (f := fun ω ↦ exp (t * (X + Y) ω)) (μ := μ)
    filter_upwards [hX_mgf, hY_mgf, hX_int, hY_int] with ω hX hY hX_int hY_int
    simp only [Pi.add_apply, NNReal.coe_add, mul_add, exp_add]
    sorry

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ} [IsFiniteMeasure μ]

-- In particular, `∑ i, Y i` is a martingale.
lemma todo (h_adapted : Adapted ℱ Y)
    (h_subG : ∀ i, IsCondSubGaussianWith (ℱ i) (ℱ.le i) (Y i) (cY i) μ) (n : ℕ) :
    IsCondSubGaussianWith (ℱ 0) (ℱ.le 0) (∑ i ∈ Finset.range n, Y i)
      (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    sorry

end Martingale

end Conditional

structure IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le_exp : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

def IsSubGaussian (X : Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, IsSubGaussianWith X c μ

lemma isSubGaussianWith_iff_kernel :
  IsSubGaussianWith X c μ
    ↔ Kernel.IsSubGaussianWith X c (Kernel.const Unit μ) (Measure.dirac ()) := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  · constructor
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
      exact (aemeasurable_of_aemeasurable_exp_mul one_ne_zero
        (h1 1).1.aemeasurable).aestronglyMeasurable
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
      exact fun t ↦ (h1 t).2
    · simpa
  · constructor
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] at h1 h2
      obtain ⟨X', hX', hXX'⟩ := h1
      refine fun t ↦ ⟨⟨fun ω ↦ exp (t * X' ω),
        continuous_exp.comp_stronglyMeasurable (hX'.const_mul t), ?_⟩, h2 t⟩
      filter_upwards [hXX'] with ω hω
      rw [hω]
    · simpa using h3

lemma isSubGaussian_iff_kernel :
  IsSubGaussian X μ ↔ Kernel.IsSubGaussian X (Kernel.const Unit μ) (Measure.dirac ()) := by
  simp_rw [IsSubGaussian, Kernel.IsSubGaussian, isSubGaussianWith_iff_kernel]

namespace IsSubGaussianWith

lemma cgf_le (h : IsSubGaussianWith X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.cgf_le t

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

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : IsSubGaussianWith X cX μ)
    (hY : IsSubGaussianWith Y cY μ) (hindep : IndepFun X Y μ) :
    IsSubGaussianWith (X + Y) (cX + cY) μ := by
  rw [isSubGaussianWith_iff_kernel] at hX hY ⊢
  simpa using hX.add_of_indepFun hY hindep

end IsSubGaussianWith

end ProbabilityTheory
