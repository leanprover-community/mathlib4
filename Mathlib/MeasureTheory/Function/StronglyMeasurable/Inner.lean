/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/

public section

variable {α 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace MeasureTheory

/-! ## Strongly measurable functions -/


local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace StronglyMeasurable

@[fun_prop]
protected theorem inner {_ : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => ⟪f t, g t⟫ :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prodMk hg)

end StronglyMeasurable

namespace AEStronglyMeasurable
variable {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E} {c : E}

@[fun_prop]
protected theorem re {f : α → 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.re (f x)) μ :=
  RCLike.continuous_re.comp_aestronglyMeasurable hf

@[fun_prop]
protected theorem im {f : α → 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.im (f x)) μ :=
  RCLike.continuous_im.comp_aestronglyMeasurable hf

@[fun_prop]
protected theorem inner {_ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
lemma inner_const (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (⟪f ·, c⟫) μ :=
  hf.inner aestronglyMeasurable_const

@[fun_prop]
lemma const_inner (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (⟪c, g ·⟫) μ :=
  aestronglyMeasurable_const.inner hg

end AEStronglyMeasurable

end MeasureTheory
