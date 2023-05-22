/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.is_R_or_C
! leanprover-community/mathlib commit 83a66c8775fa14ee5180c85cab98e970956401ad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.SpecialFunctions.Basic
import Mathbin.Data.IsROrC.Lemmas

/-!
# Measurability of the basic `is_R_or_C` functions

-/


noncomputable section

open NNReal ENNReal

namespace IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜]

@[measurability]
theorem measurable_re : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.Measurable
#align is_R_or_C.measurable_re IsROrC.measurable_re

@[measurability]
theorem measurable_im : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.Measurable
#align is_R_or_C.measurable_im IsROrC.measurable_im

end IsROrC

section IsROrCComposition

variable {α 𝕜 : Type _} [IsROrC 𝕜] {m : MeasurableSpace α} {f : α → 𝕜} {μ : MeasureTheory.Measure α}

include m

@[measurability]
theorem Measurable.re (hf : Measurable f) : Measurable fun x => IsROrC.re (f x) :=
  IsROrC.measurable_re.comp hf
#align measurable.re Measurable.re

@[measurability]
theorem AEMeasurable.re (hf : AEMeasurable f μ) : AEMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.measurable_re.comp_aemeasurable hf
#align ae_measurable.re AEMeasurable.re

@[measurability]
theorem Measurable.im (hf : Measurable f) : Measurable fun x => IsROrC.im (f x) :=
  IsROrC.measurable_im.comp hf
#align measurable.im Measurable.im

@[measurability]
theorem AEMeasurable.im (hf : AEMeasurable f μ) : AEMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.measurable_im.comp_aemeasurable hf
#align ae_measurable.im AEMeasurable.im

omit m

end IsROrCComposition

section

variable {α 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[measurability]
theorem IsROrC.measurable_of_real : Measurable (coe : ℝ → 𝕜) :=
  IsROrC.continuous_ofReal.Measurable
#align is_R_or_C.measurable_of_real IsROrC.measurable_of_real

theorem measurable_of_re_im (hre : Measurable fun x => IsROrC.re (f x))
    (him : Measurable fun x => IsROrC.im (f x)) : Measurable f :=
  by
  convert(is_R_or_C.measurable_of_real.comp hre).add
      ((is_R_or_C.measurable_of_real.comp him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
  all_goals infer_instance
#align measurable_of_re_im measurable_of_re_im

theorem aEMeasurable_of_re_im (hre : AEMeasurable (fun x => IsROrC.re (f x)) μ)
    (him : AEMeasurable (fun x => IsROrC.im (f x)) μ) : AEMeasurable f μ :=
  by
  convert(is_R_or_C.measurable_of_real.comp_ae_measurable hre).add
      ((is_R_or_C.measurable_of_real.comp_ae_measurable him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
  all_goals infer_instance
#align ae_measurable_of_re_im aEMeasurable_of_re_im

end

