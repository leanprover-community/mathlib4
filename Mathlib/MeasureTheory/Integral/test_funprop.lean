import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.Chebyshev


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E F : Type*} {mα : MeasurableSpace α}

variable [NormedAddCommGroup E] {f g : α → ε} {s t : Set α} {μ ν : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']


attribute [fun_prop] IntegrableOn IntegrableOn.integrable integrableOn_empty
  IntegrableOn.restrict IntegrableOn.inter_of_restrict IntegrableOn.left_of_union
  IntegrableOn.right_of_union IntegrableOn.union IntegrableOn.add_measure
  IntegrableOn.fun_add IntegrableOn.fun_sub IntegrableOn.fun_neg IntegrableOn.fun_add
  IntegrableOn.integrable_indicator
  IntegrableOn.integrable_indicator₀
  IntegrableOn.indicator
  Integrable.integrableOn
  Continuous.integrableOn_Icc Continuous.integrableOn_Ioc Continuous.integrableOn_uIcc
  Continuous.integrableOn_Ioc
  IntegrableOn.mono IntegrableOn.mono_set IntegrableOn.mono_measure

section missing_lemmas

@[fun_prop]
theorem IntegrableOn.indicator₀ {f : α → ε'} (h : IntegrableOn f s μ)
    (ht : NullMeasurableSet t <| μ.restrict s) :
    IntegrableOn (indicator t f) s μ :=
  Integrable.indicator₀ h ht

@[fun_prop]
theorem IntegrableOn.univ (h : IntegrableOn f univ μ) : Integrable f μ :=
  integrableOn_univ.mp h

@[fun_prop]
theorem IntegrableOn.left_inter (h : IntegrableOn f s μ) : IntegrableOn f (s ∩ t) μ :=
  h.mono_set inter_subset_left

@[fun_prop]
theorem IntegrableOn.right_inter (h : IntegrableOn f t μ) : IntegrableOn f (s ∩ t) μ :=
  h.mono_set inter_subset_right

@[fun_prop]
protected theorem IntegrableOn.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α → E} (hf : IntegrableOn f s μ) (c : 𝕜) :
    IntegrableOn (fun x ↦ c • f x) s μ := by
  rw [IntegrableOn] at *
  exact Integrable.smul c hf

@[fun_prop]
protected theorem IntegrableOn.const_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α → 𝕜} (hf : IntegrableOn f s μ) (c : E) :
    IntegrableOn (fun x ↦ f x • c) s μ := by
  rw [IntegrableOn] at *
  exact Integrable.smul_const hf c

end missing_lemmas

section testing

variable [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

variable {f g : α → ε'}

example [ContinuousAdd ε'] (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x ↦ f x + g x) s μ := by
  fun_prop

example [ContinuousAdd ε'] (hf : IntegrableOn f s μ) (hg : Integrable g μ) :
    IntegrableOn (fun x ↦ f x + g x) s μ := by
  fun_prop

example [ContinuousAdd ε'] (ht : MeasurableSet t) (hf : IntegrableOn f s μ) (hg : Integrable g μ) :
    IntegrableOn (fun x ↦ f x + t.indicator g x) s μ := by
  fun_prop (disch := measurability)

example [ContinuousAdd ε'] (ht : NullMeasurableSet t <| μ.restrict s) (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x ↦ f x + t.indicator g x) s μ := by
  fun_prop (disch := measurability)

example [ContinuousAdd ε'] (hf : IntegrableOn f s μ) (hg : IntegrableOn g t μ) :
    IntegrableOn (fun x ↦ f x + g x) (s ∩ t) μ := by
  fun_prop

example {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α → E} (hf : IntegrableOn f s μ) (c : 𝕜) :
    IntegrableOn (fun x ↦ c • f x) (s ∩ t) μ := by
  fun_prop

end testing

section more_missing

@[fun_prop]
theorem continuous_complex_ofReal : Continuous Complex.ofReal := Complex.ofRealCLM.cont

@[fun_prop]
theorem integrableOn_complex_ofReal (s : Set ℝ) : IntegrableOn Complex.ofReal s :=
  by sorry --Complex.ofRealCLM.cont

end more_missing

section IntegrableOn

example (a b : ℝ) : IntegrableOn (fun x : ℝ => Real.sin x + x ^ 2) (Icc a b) := by
  fun_prop

example (a b : ℝ) : IntegrableOn (fun x : ℝ => Real.exp x) (Icc a b) := by
  fun_prop

example (a b : ℝ) : IntegrableOn (fun x : ℝ => (x, Real.exp x)) (Icc a b) := by
  fun_prop

example (a b : ℝ) : IntegrableOn (fun x : ℝ => (Real.sin x : ℂ)) (Icc a b) := by
  fail_if_success fun_prop
  sorry

example {f : ℝ → ℝ} {s t : Set ℝ} (hf : IntegrableOn f t) (hst : s ⊆ t) : IntegrableOn f s := by
  fun_prop (disch := with_reducible assumption)

example : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
  fail_if_success fun_prop
  sorry

example (c : ℝ) : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi c) := by
  fail_if_success fun_prop
  sorry

example (c : ℝ) : IntegrableOn Real.exp (Iic c) := by
  fail_if_success fun_prop
  sorry

example {s : ℝ} (hs : s < -1) : IntegrableOn (fun x : ℝ => x ^ s) (Ioi 1) := by
  fail_if_success fun_prop
  sorry

example {s t : ℝ} (ht : 0 < t) (hs : -1 < s) : IntegrableOn (fun x : ℝ => x ^ s) (Ioo 0 t) := by
  fail_if_success fun_prop
  sorry
