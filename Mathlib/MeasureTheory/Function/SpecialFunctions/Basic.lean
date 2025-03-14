/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `MeasureTheory.Function.SpecialFunctions.Arctan` and
`MeasureTheory.Function.SpecialFunctions.Inner`, which have been split off to minimize imports.
-/

-- Guard against import creep:
assert_not_exists InnerProductSpace Real.arctan FiniteDimensional.proper

noncomputable section

open NNReal ENNReal MeasureTheory

namespace Real

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : MeasureTheory.Measure α}

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable

@[measurability]
theorem measurable_log : Measurable log :=
  measurable_of_measurable_on_compl_singleton 0 <|
    Continuous.measurable <| continuousOn_iff_continuous_restrict.1 continuousOn_log

lemma measurable_of_measurable_exp (hf : Measurable (fun x ↦ exp (f x))) :
    Measurable f := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

lemma aemeasurable_of_aemeasurable_exp_mul {t : ℝ}
    (ht : t ≠ 0) (hf : AEMeasurable (fun x ↦ exp (t * f x)) μ) :
    AEMeasurable f μ := by
  simpa only [mul_div_cancel_left₀ _ ht]
    using (aemeasurable_of_aemeasurable_exp hf).div (aemeasurable_const (b := t))

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable

@[measurability]
theorem measurable_arcsin : Measurable arcsin :=
  continuous_arcsin.measurable

@[measurability]
theorem measurable_arccos : Measurable arccos :=
  continuous_arccos.measurable

end Real

namespace Complex

@[measurability]
theorem measurable_re : Measurable re :=
  continuous_re.measurable

@[measurability]
theorem measurable_im : Measurable im :=
  continuous_im.measurable

@[measurability]
theorem measurable_ofReal : Measurable ((↑) : ℝ → ℂ) :=
  continuous_ofReal.measurable

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable

@[measurability]
theorem measurable_arg : Measurable arg :=
  have A : Measurable fun x : ℂ => Real.arcsin (x.im / ‖x‖) :=
    Real.measurable_arcsin.comp (measurable_im.div measurable_norm)
  have B : Measurable fun x : ℂ => Real.arcsin ((-x).im / ‖x‖) :=
    Real.measurable_arcsin.comp ((measurable_im.comp measurable_neg).div measurable_norm)
  Measurable.ite (isClosed_le continuous_const continuous_re).measurableSet A <|
    Measurable.ite (isClosed_le continuous_const continuous_im).measurableSet (B.add_const _)
      (B.sub_const _)

@[measurability]
theorem measurable_log : Measurable log :=
  (measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add <|
    (measurable_ofReal.comp measurable_arg).mul_const I

end Complex

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)
include hf

@[measurability, fun_prop]
protected theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurable_exp.comp hf

@[measurability, fun_prop]
protected theorem Measurable.log : Measurable fun x => log (f x) :=
  measurable_log.comp hf

@[measurability, fun_prop]
protected theorem Measurable.cos : Measurable fun x ↦ cos (f x) := measurable_cos.comp hf

@[measurability, fun_prop]
protected theorem Measurable.sin : Measurable fun x ↦ sin (f x) := measurable_sin.comp hf

@[measurability, fun_prop]
protected theorem Measurable.cosh : Measurable fun x ↦ cosh (f x) := measurable_cosh.comp hf

@[measurability, fun_prop]
protected theorem Measurable.sinh : Measurable fun x ↦ sinh (f x) := measurable_sinh.comp hf

@[measurability, fun_prop]
protected theorem Measurable.sqrt : Measurable fun x => √(f x) := continuous_sqrt.measurable.comp hf

end RealComposition

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ)
include hf

@[measurability, fun_prop]
protected lemma AEMeasurable.exp : AEMeasurable (fun x ↦ exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.log : AEMeasurable (fun x ↦ log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.cos : AEMeasurable (fun x ↦ cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.sin : AEMeasurable (fun x ↦ sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.cosh : AEMeasurable (fun x ↦ cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.sinh : AEMeasurable (fun x ↦ sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.sqrt : AEMeasurable (fun x ↦ √(f x)) μ :=
  continuous_sqrt.measurable.comp_aemeasurable hf

end RealComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)
include hf

@[measurability, fun_prop]
protected theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurable_exp.comp hf

@[measurability, fun_prop]
protected theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurable_cos.comp hf

@[measurability, fun_prop]
protected theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurable_sin.comp hf

@[measurability, fun_prop]
protected theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurable_cosh.comp hf

@[measurability, fun_prop]
protected theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurable_sinh.comp hf

@[measurability, fun_prop]
protected theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurable_arg.comp hf

@[measurability, fun_prop]
protected theorem Measurable.clog : Measurable fun x => Complex.log (f x) :=
  measurable_log.comp hf

end ComplexComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℂ} (hf : AEMeasurable f μ)
include hf

@[measurability, fun_prop]
protected lemma AEMeasurable.cexp : AEMeasurable (fun x ↦ exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.ccos : AEMeasurable (fun x ↦ cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.csin : AEMeasurable (fun x ↦ sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.ccosh : AEMeasurable (fun x ↦ cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.csinh : AEMeasurable (fun x ↦ sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.carg : AEMeasurable (fun x ↦ arg (f x)) μ :=
  measurable_arg.comp_aemeasurable hf

@[measurability, fun_prop]
protected lemma AEMeasurable.clog : AEMeasurable (fun x ↦ log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

end ComplexComposition

@[measurability, fun_prop]
protected theorem Measurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}
    (hf : Measurable f) :
    Measurable fun x ↦ (f x : ℂ) :=
  Complex.measurable_ofReal.comp hf

@[measurability, fun_prop]
protected theorem AEMeasurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x : ℂ)) μ :=
  Complex.measurable_ofReal.comp_aemeasurable hf

section PowInstances

instance Complex.hasMeasurablePow : MeasurablePow ℂ ℂ :=
  ⟨Measurable.ite (measurable_fst (measurableSet_singleton 0))
      (Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_one measurable_zero)
      (measurable_fst.clog.mul measurable_snd).cexp⟩

instance Real.hasMeasurablePow : MeasurablePow ℝ ℝ :=
  ⟨Complex.measurable_re.comp <|
      (Complex.measurable_ofReal.comp measurable_fst).pow
        (Complex.measurable_ofReal.comp measurable_snd)⟩

instance NNReal.hasMeasurablePow : MeasurablePow ℝ≥0 ℝ :=
  ⟨(measurable_fst.coe_nnreal_real.pow measurable_snd).subtype_mk⟩

instance ENNReal.hasMeasurablePow : MeasurablePow ℝ≥0∞ ℝ := by
  refine ⟨ENNReal.measurable_of_measurable_nnreal_prod ?_ ?_⟩
  · simp_rw [ENNReal.coe_rpow_def]
    refine Measurable.ite ?_ measurable_const (measurable_fst.pow measurable_snd).coe_nnreal_ennreal
    exact
      MeasurableSet.inter (measurable_fst (measurableSet_singleton 0))
        (measurable_snd measurableSet_Iio)
  · simp_rw [ENNReal.top_rpow_def]
    refine Measurable.ite measurableSet_Ioi measurable_const ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

end PowInstances
