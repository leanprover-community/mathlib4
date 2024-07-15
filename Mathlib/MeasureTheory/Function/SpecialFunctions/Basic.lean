/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

#align_import measure_theory.function.special_functions.basic from "leanprover-community/mathlib"@"83a66c8775fa14ee5180c85cab98e970956401ad"

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `MeasureTheory.Function.SpecialFunctions.Arctan` and
`MeasureTheory.Function.SpecialFunctions.Inner`, which have been split off to minimize imports.
-/


noncomputable section

open NNReal ENNReal

namespace Real

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable
#align real.measurable_exp Real.measurable_exp

@[measurability]
theorem measurable_log : Measurable log :=
  measurable_of_measurable_on_compl_singleton 0 <|
    Continuous.measurable <| continuousOn_iff_continuous_restrict.1 continuousOn_log
#align real.measurable_log Real.measurable_log

lemma measurable_of_measurable_exp {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ}
    (hf : Measurable (fun x ↦ exp (f x))) :
    Measurable f := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

lemma aemeasurable_of_aemeasurable_exp {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ}
    {μ : MeasureTheory.Measure α} (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable
#align real.measurable_sin Real.measurable_sin

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable
#align real.measurable_cos Real.measurable_cos

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable
#align real.measurable_sinh Real.measurable_sinh

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable
#align real.measurable_cosh Real.measurable_cosh

@[measurability]
theorem measurable_arcsin : Measurable arcsin :=
  continuous_arcsin.measurable
#align real.measurable_arcsin Real.measurable_arcsin

@[measurability]
theorem measurable_arccos : Measurable arccos :=
  continuous_arccos.measurable
#align real.measurable_arccos Real.measurable_arccos

end Real

namespace Complex

@[measurability]
theorem measurable_re : Measurable re :=
  continuous_re.measurable
#align complex.measurable_re Complex.measurable_re

@[measurability]
theorem measurable_im : Measurable im :=
  continuous_im.measurable
#align complex.measurable_im Complex.measurable_im

@[measurability]
theorem measurable_ofReal : Measurable ((↑) : ℝ → ℂ) :=
  continuous_ofReal.measurable
#align complex.measurable_of_real Complex.measurable_ofReal

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable
#align complex.measurable_exp Complex.measurable_exp

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable
#align complex.measurable_sin Complex.measurable_sin

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable
#align complex.measurable_cos Complex.measurable_cos

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable
#align complex.measurable_sinh Complex.measurable_sinh

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable
#align complex.measurable_cosh Complex.measurable_cosh

@[measurability]
theorem measurable_arg : Measurable arg :=
  have A : Measurable fun x : ℂ => Real.arcsin (x.im / Complex.abs x) :=
    Real.measurable_arcsin.comp (measurable_im.div measurable_norm)
  have B : Measurable fun x : ℂ => Real.arcsin ((-x).im / Complex.abs x) :=
    Real.measurable_arcsin.comp ((measurable_im.comp measurable_neg).div measurable_norm)
  Measurable.ite (isClosed_le continuous_const continuous_re).measurableSet A <|
    Measurable.ite (isClosed_le continuous_const continuous_im).measurableSet (B.add_const _)
      (B.sub_const _)
#align complex.measurable_arg Complex.measurable_arg

@[measurability]
theorem measurable_log : Measurable log :=
  (measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add <|
    (measurable_ofReal.comp measurable_arg).mul_const I
#align complex.measurable_log Complex.measurable_log

end Complex

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

@[measurability]
theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurable_exp.comp hf
#align measurable.exp Measurable.exp

@[measurability]
theorem Measurable.log : Measurable fun x => log (f x) :=
  measurable_log.comp hf
#align measurable.log Measurable.log

@[measurability]
theorem Measurable.cos : Measurable fun x => Real.cos (f x) :=
  Real.measurable_cos.comp hf
#align measurable.cos Measurable.cos

@[measurability]
theorem Measurable.sin : Measurable fun x => Real.sin (f x) :=
  Real.measurable_sin.comp hf
#align measurable.sin Measurable.sin

@[measurability]
theorem Measurable.cosh : Measurable fun x => Real.cosh (f x) :=
  Real.measurable_cosh.comp hf
#align measurable.cosh Measurable.cosh

@[measurability]
theorem Measurable.sinh : Measurable fun x => Real.sinh (f x) :=
  Real.measurable_sinh.comp hf
#align measurable.sinh Measurable.sinh

@[measurability]
theorem Measurable.sqrt : Measurable fun x => √(f x) :=
  continuous_sqrt.measurable.comp hf
#align measurable.sqrt Measurable.sqrt

end RealComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)

@[measurability]
theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurable_exp.comp hf
#align measurable.cexp Measurable.cexp

@[measurability]
theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurable_cos.comp hf
#align measurable.ccos Measurable.ccos

@[measurability]
theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurable_sin.comp hf
#align measurable.csin Measurable.csin

@[measurability]
theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurable_cosh.comp hf
#align measurable.ccosh Measurable.ccosh

@[measurability]
theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurable_sinh.comp hf
#align measurable.csinh Measurable.csinh

@[measurability]
theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurable_arg.comp hf
#align measurable.carg Measurable.carg

@[measurability]
theorem Measurable.clog : Measurable fun x => Complex.log (f x) :=
  measurable_log.comp hf
#align measurable.clog Measurable.clog

end ComplexComposition

section PowInstances

instance Complex.hasMeasurablePow : MeasurablePow ℂ ℂ :=
  ⟨Measurable.ite (measurable_fst (measurableSet_singleton 0))
      (Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_one measurable_zero)
      (measurable_fst.clog.mul measurable_snd).cexp⟩
#align complex.has_measurable_pow Complex.hasMeasurablePow

instance Real.hasMeasurablePow : MeasurablePow ℝ ℝ :=
  ⟨Complex.measurable_re.comp <|
      (Complex.measurable_ofReal.comp measurable_fst).pow
        (Complex.measurable_ofReal.comp measurable_snd)⟩
#align real.has_measurable_pow Real.hasMeasurablePow

instance NNReal.hasMeasurablePow : MeasurablePow ℝ≥0 ℝ :=
  ⟨(measurable_fst.coe_nnreal_real.pow measurable_snd).subtype_mk⟩
#align nnreal.has_measurable_pow NNReal.hasMeasurablePow

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
#align ennreal.has_measurable_pow ENNReal.hasMeasurablePow

end PowInstances

-- Guard against import creep:
assert_not_exists InnerProductSpace
assert_not_exists Real.arctan
assert_not_exists FiniteDimensional.proper
