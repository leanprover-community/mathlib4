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

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

open scoped ZeroAtInfty Filter Topology BoundedContinuousFunction

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def Lp.fourierTransform (f : Lp (α := V) E 1) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V → E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (L1.integrable_coeFn f))
  ‖f‖
  (by
    intro x
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le)

@[norm_cast]
theorem Lp.coe_fourierTransform (f : Lp (α := V) E 1) :
    (Lp.fourierTransform f : V → E) = 𝓕 (f : V → E) := rfl

@[simp]
theorem Lp.fourierTransform_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransform f x = 𝓕 (f : V → E) x := rfl

@[simp]
theorem fourier_toLp {f : V → E} (hf : MemLp f 1) :
    (Lp.fourierTransform hf.toLp : V → E) = 𝓕 f := by
  simp only [Lp.coe_fourierTransform]
  ext x
  apply (Real.fourier_congr_ae hf.coeFn_toLp)

def _root_.LinearMap.mkContinuous' [NormedSpace ℂ V] (f : V → E)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hsmul : ∀ (c : ℂ) a, f (c • a) = c • f a)
    (C : ℝ)
    (hbound : ∀ a, ‖f a‖ ≤ C * ‖a‖) : V →L[ℂ] E :=
  LinearMap.mkContinuous {toFun := f, map_add' := hadd, map_smul' := hsmul} C hbound

def Lp.fourierTransformCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  LinearMap.mkContinuous' Lp.fourierTransform
  (by
    intro f g
    ext x
    simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
      Real.fourier_eq]
    rw [← integral_add]
    · apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with x h₁
      rw [h₁]
      simp
    · rw [Real.fourierIntegral_convergent_iff]
      exact L1.integrable_coeFn f
    · rw [Real.fourierIntegral_convergent_iff]
      exact L1.integrable_coeFn g)
  (by
    intro c f
    ext x
    simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_smul, Real.fourier_eq]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x h
    rw [h, smul_comm]
    simp )
  1 (by
    intro f
    rw [one_mul, BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    rw [Lp.fourierTransform_apply, Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le)

@[simp]
theorem Lp.fourierTransformCLM_apply (f : Lp (α := V) E 1) :
  Lp.fourierTransformCLM f = Lp.fourierTransform f := rfl

variable [CompleteSpace E]

variable (V E) in
/-- The Fourier transform on `L1` as a linear isometry equivalence. -/
def Lp.fourierTransformZeroAtInftyCLM : (Lp (α := V) E 1) →L[ℂ] C₀(V, E) :=
  (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := V) E 1)

@[simp]
theorem Lp.fourierTransformZeroAtInftyCLM_toLp_one_apply (f : 𝓢(V, E)) (x : V) :
    Lp.fourierTransformZeroAtInftyCLM V E (f.toLp 1) x = 𝓕 f x := by
  calc
    _ = ((fourierTransformZeroAtInftyCLM V E) (toLpCLM ℂ (E := V) E 1 volume f)) x := by simp
    _ = (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap f x := by
      congr 1
      apply LinearMap.extendOfNorm_eq
      · apply SchwartzMap.denseRange_toLpCLM
        norm_num
      use 1
      simpa using norm_fourier_toBoundedContinuousFunction_le_toLp_one
    _ = 𝓕 f x := by simp

theorem Lp.fourierTransformZeroAtInftyCLM_toBCF (f : Lp (α := V) E 1) :
    (Lp.fourierTransformZeroAtInftyCLM V E f).toBCF = Lp.fourierTransform f := by
  apply (denseRange_toLpCLM (by norm_num)).induction_on
    (p := fun f ↦ (Lp.fourierTransformZeroAtInftyCLM V E f).toBCF = Lp.fourierTransform f) f
    (isClosed_eq (by fun_prop) Lp.fourierTransformCLM.cont)
  intro f
  ext x
  simpa using Real.fourier_congr_ae (coeFn_toLp f 1 volume).symm x

theorem Lp.fourierTransformZeroAtInftyCLM_apply_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformZeroAtInftyCLM V E f x = 𝓕 (f : V → E) x := by
  rw [← ZeroAtInftyContinuousMap.toBCF_apply, Lp.fourierTransformZeroAtInftyCLM_toBCF]
  simp

theorem riemann_lebesgue (f : V → E) (hf : MemLp f 1) :
    Filter.Tendsto (𝓕 f) (Filter.cocompact V) (𝓝 0) := by
  rw [← fourier_toLp hf, ← Lp.fourierTransformZeroAtInftyCLM_toBCF]
  apply zero_at_infty ((Lp.fourierTransformZeroAtInftyCLM V E) (hf.toLp f))
