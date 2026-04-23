/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Batteries.Tactic.Congr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Real
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
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Integrals with a measure derived from probability mass functions.

This file connects `PMF` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `PMF` is a sum weighted by the `PMF`.

It also provides the expected value for specific probability mass functions.
-/

public section

namespace PMF

open MeasureTheory NNReal ENNReal TopologicalSpace

section General

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_eq_tsum (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply setIntegral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr 2
    apply PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
    tsum_subtype_eq_of_support_subset <| calc
      (fun a ↦ (p a).toReal • f a).support ⊆ (fun a ↦ (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ ⊆ support p := fun x h1 h2 => h1 (by simp [h2])

theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [integral_fintype .of_finite]
  congr with x
  rw [measureReal_def]
  congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

end General

theorem bernoulli_expectation {p : ℝ≥0} (h : p ≤ 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by simp [integral_eq_sum]

end PMF
