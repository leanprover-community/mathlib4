/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public noncomputable section

section FourierTransform

variable
  {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

open scoped ZeroAtInfty Filter Topology BoundedContinuousFunction ENNReal

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (V E) in
/-- The Fourier transform on `L1` as a linear isometry equivalence. -/
def Lp.fourierTransformCLM : (Lp (α := V) E 1) →L[ℂ] C₀(V, E) :=
  (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := V) E 1)

def foo₀ (f : Lp (α := V) E 1) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V → E))
  (by
    apply VectorFourier.fourierIntegral_continuous
    · exact Real.continuous_fourierChar
    · exact (innerSL ℝ).continuous₂
    exact L1.integrable_coeFn f)
  ‖f‖
  (by
    intro x
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le)

@[simp]
theorem foo₀_apply (f : Lp (α := V) E 1) (x : V) : foo₀ f x = 𝓕 (f : V → E) x := rfl

def fooₗ : Lp (α := V) E 1 →ₗ[ℂ] V →ᵇ E where
  toFun f := foo₀ f
  map_add' f g := by
    ext x
    simp only [foo₀_apply, BoundedContinuousFunction.coe_add, Pi.add_apply]
    simp_rw [Real.fourier_eq]
    rw [← integral_add]
    · apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with x h₁
      rw [h₁]
      simp
    · rw [Real.fourierIntegral_convergent_iff]
      exact L1.integrable_coeFn f
    · rw [Real.fourierIntegral_convergent_iff]
      exact L1.integrable_coeFn g
  map_smul' c f := by
    ext x
    simp only [foo₀_apply, RingHom.id_apply, BoundedContinuousFunction.coe_smul]
    simp_rw [Real.fourier_eq]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x h
    rw [h, smul_comm]
    simp

theorem fooₗ_apply (f : Lp (α := V) E 1) : fooₗ f = foo₀ f := rfl

def foo : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  LinearMap.mkContinuous fooₗ 1
  (by
    intro f
    rw [one_mul, BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    rw [fooₗ_apply, foo₀_apply, Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le)

@[simp]
theorem foo_apply (f : Lp (α := V) E 1) : foo f = foo₀ f := rfl

@[simp]
theorem Lp.fourierTransformCLM_toLp_one_apply (f : 𝓢(V, E)) (x : V) :
    Lp.fourierTransformCLM V E (f.toLp 1) x = 𝓕 f x := by
  have lhs :
      (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap f x = 𝓕 f x := by
    simp
  have rhs : toLpCLM ℂ (E := V) E 1 volume f = f.toLp 1 := by simp
  rw [← lhs, ← rhs]
  congr 1
  apply LinearMap.extendOfNorm_eq
  · apply SchwartzMap.denseRange_toLpCLM
    norm_num
  use 1
  simpa using norm_fourier_toBoundedContinuousFunction_le_toLp_one

theorem Lp.fourierTransformCLM_toBCF (f : Lp (α := V) E 1) :
    (Lp.fourierTransformCLM V E f).toBCF = foo f := by
  apply (denseRange_toLpCLM (by norm_num)).induction_on
    (p := fun f ↦ (Lp.fourierTransformCLM V E f).toBCF = foo f) f
    (isClosed_eq (by fun_prop) foo.cont)
  intro f
  ext x
  simpa using Real.fourier_congr_ae (coeFn_toLp f 1 volume).symm x

theorem Lp.fourierTransformCLM_apply_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformCLM V E f x = 𝓕 (f : V → E) x := by
  rw [← ZeroAtInftyContinuousMap.toBCF_apply, Lp.fourierTransformCLM_toBCF]
  simp

theorem riemann_lebesgue (f : V → E) (hf : MemLp f 1) :
    Filter.Tendsto (𝓕 f) (Filter.cocompact V) (𝓝 0) := by
  have : Lp.fourierTransformCLM V E hf.toLp = 𝓕 f := by
    ext x
    rw [Lp.fourierTransformCLM_apply_apply hf.toLp]
    apply Real.fourier_congr_ae hf.coeFn_toLp
  rw [← this]
  apply zero_at_infty
