/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of the basic `RCLike` functions

-/

@[expose] public section


noncomputable section

open NNReal ENNReal

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

@[measurability]
theorem measurable_re : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.measurable

@[measurability]
theorem measurable_im : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.measurable

end RCLike

section RCLikeComposition

variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {f : α → 𝕜}
  {μ : MeasureTheory.Measure α}

@[fun_prop]
theorem Measurable.re (hf : Measurable f) : Measurable fun x => RCLike.re (f x) :=
  RCLike.measurable_re.comp hf

@[fun_prop]
theorem AEMeasurable.re (hf : AEMeasurable f μ) : AEMeasurable (fun x => RCLike.re (f x)) μ :=
  RCLike.measurable_re.comp_aemeasurable hf

@[fun_prop]
theorem Measurable.im (hf : Measurable f) : Measurable fun x => RCLike.im (f x) :=
  RCLike.measurable_im.comp hf

@[fun_prop]
theorem AEMeasurable.im (hf : AEMeasurable f μ) : AEMeasurable (fun x => RCLike.im (f x)) μ :=
  RCLike.measurable_im.comp_aemeasurable hf

end RCLikeComposition

section

variable {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[fun_prop]
theorem RCLike.measurable_ofReal : Measurable ((↑) : ℝ → 𝕜) :=
  RCLike.continuous_ofReal.measurable

theorem measurable_of_re_im (hre : Measurable fun x => RCLike.re (f x))
    (him : Measurable fun x => RCLike.im (f x)) : Measurable f := by
  convert Measurable.add (M := 𝕜) (RCLike.measurable_ofReal.comp hre)
      ((RCLike.measurable_ofReal.comp him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

theorem aemeasurable_of_re_im (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => RCLike.im (f x)) μ) : AEMeasurable f μ := by
  convert AEMeasurable.add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

end
