/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

#align_import measure_theory.function.strongly_measurable.inner from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/


variable {α : Type*}

namespace MeasureTheory

/-! ## Strongly measurable functions -/


namespace StronglyMeasurable

protected theorem inner {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {_ : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prod_mk hg)
#align measure_theory.strongly_measurable.inner MeasureTheory.StronglyMeasurable.inner

end StronglyMeasurable

namespace AEStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

protected theorem re {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => RCLike.re (f x)) μ :=
  RCLike.continuous_re.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.re MeasureTheory.AEStronglyMeasurable.re

protected theorem im {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => RCLike.im (f x)) μ :=
  RCLike.continuous_im.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.im MeasureTheory.AEStronglyMeasurable.im

protected theorem inner {_ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.inner MeasureTheory.AEStronglyMeasurable.inner

end AEStronglyMeasurable

end MeasureTheory
