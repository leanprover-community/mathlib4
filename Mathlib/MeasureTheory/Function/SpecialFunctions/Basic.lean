/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.basic
! leanprover-community/mathlib commit 83a66c8775fa14ee5180c85cab98e970956401ad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Nnreal
import Mathbin.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `measure_theory.function.special_functions.arctan` and
`measure_theory.function.special_functions.inner`, which have been split off to minimize imports.
-/


noncomputable section

open NNReal ENNReal

namespace Real

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.Measurable
#align real.measurable_exp Real.measurable_exp

@[measurability]
theorem measurable_log : Measurable log :=
  measurable_of_measurable_on_compl_singleton 0 <|
    Continuous.measurable <| continuousOn_iff_continuous_restrict.1 continuousOn_log
#align real.measurable_log Real.measurable_log

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.Measurable
#align real.measurable_sin Real.measurable_sin

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.Measurable
#align real.measurable_cos Real.measurable_cos

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.Measurable
#align real.measurable_sinh Real.measurable_sinh

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.Measurable
#align real.measurable_cosh Real.measurable_cosh

@[measurability]
theorem measurable_arcsin : Measurable arcsin :=
  continuous_arcsin.Measurable
#align real.measurable_arcsin Real.measurable_arcsin

@[measurability]
theorem measurable_arccos : Measurable arccos :=
  continuous_arccos.Measurable
#align real.measurable_arccos Real.measurable_arccos

end Real

namespace Complex

@[measurability]
theorem measurable_re : Measurable re :=
  continuous_re.Measurable
#align complex.measurable_re Complex.measurable_re

@[measurability]
theorem measurable_im : Measurable im :=
  continuous_im.Measurable
#align complex.measurable_im Complex.measurable_im

@[measurability]
theorem measurable_of_real : Measurable (coe : ℝ → ℂ) :=
  continuous_ofReal.Measurable
#align complex.measurable_of_real Complex.measurable_of_real

@[measurability]
theorem measurable_exp : Measurable exp :=
  continuous_exp.Measurable
#align complex.measurable_exp Complex.measurable_exp

@[measurability]
theorem measurable_sin : Measurable sin :=
  continuous_sin.Measurable
#align complex.measurable_sin Complex.measurable_sin

@[measurability]
theorem measurable_cos : Measurable cos :=
  continuous_cos.Measurable
#align complex.measurable_cos Complex.measurable_cos

@[measurability]
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.Measurable
#align complex.measurable_sinh Complex.measurable_sinh

@[measurability]
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.Measurable
#align complex.measurable_cosh Complex.measurable_cosh

@[measurability]
theorem measurable_arg : Measurable arg :=
  have A : Measurable fun x : ℂ => Real.arcsin (x.im / x.abs) :=
    Real.measurable_arcsin.comp (measurable_im.div measurable_norm)
  have B : Measurable fun x : ℂ => Real.arcsin ((-x).im / x.abs) :=
    Real.measurable_arcsin.comp ((measurable_im.comp measurable_neg).div measurable_norm)
  Measurable.ite (isClosed_le continuous_const continuous_re).MeasurableSet A <|
    Measurable.ite (isClosed_le continuous_const continuous_im).MeasurableSet (B.AddConst _)
      (B.sub_const _)
#align complex.measurable_arg Complex.measurable_arg

@[measurability]
theorem measurable_log : Measurable log :=
  (measurable_of_real.comp <| Real.measurable_log.comp measurable_norm).add <|
    (measurable_of_real.comp measurable_arg).mul_const I
#align complex.measurable_log Complex.measurable_log

end Complex

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

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
theorem Measurable.sqrt : Measurable fun x => sqrt (f x) :=
  continuous_sqrt.Measurable.comp hf
#align measurable.sqrt Measurable.sqrt

end RealComposition

section ComplexComposition

open Complex

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)

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
theorem Measurable.clog : Measurable fun x => log (f x) :=
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
      (Complex.measurable_of_real.comp measurable_fst).pow
        (Complex.measurable_of_real.comp measurable_snd)⟩
#align real.has_measurable_pow Real.hasMeasurablePow

instance NNReal.hasMeasurablePow : MeasurablePow ℝ≥0 ℝ :=
  ⟨(measurable_fst.coeNNRealReal.pow measurable_snd).subtype_mk⟩
#align nnreal.has_measurable_pow NNReal.hasMeasurablePow

instance ENNReal.hasMeasurablePow : MeasurablePow ℝ≥0∞ ℝ :=
  by
  refine' ⟨ENNReal.measurable_of_measurable_nnreal_prod _ _⟩
  · simp_rw [ENNReal.coe_rpow_def]
    refine' Measurable.ite _ measurable_const (measurable_fst.pow measurable_snd).coe_nnreal_ennreal
    exact
      MeasurableSet.inter (measurable_fst (measurable_set_singleton 0))
        (measurable_snd measurableSet_Iio)
  · simp_rw [ENNReal.top_rpow_def]
    refine' Measurable.ite measurableSet_Ioi measurable_const _
    exact Measurable.ite (measurable_set_singleton 0) measurable_const measurable_const
#align ennreal.has_measurable_pow ENNReal.hasMeasurablePow

end PowInstances

-- Guard against import creep:
assert_not_exists inner_product_space

assert_not_exists real.arctan

assert_not_exists FiniteDimensional.proper

