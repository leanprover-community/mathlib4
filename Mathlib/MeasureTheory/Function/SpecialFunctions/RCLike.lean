/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Measurability of the basic `RCLike` functions

-/

public section


noncomputable section

open NNReal ENNReal

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

theorem measurable_re : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.measurable

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
