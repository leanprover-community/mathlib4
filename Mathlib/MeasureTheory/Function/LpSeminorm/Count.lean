/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Order.Filter.Map
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
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# `L^p`-seminorms on `count` and `dirac`
-/

@[expose] public section

open MeasureTheory Measure ENNReal Set Filter
variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p : ℝ≥0∞} {x : α}

namespace MeasureTheory

@[simp]
lemma eLpNorm_dirac (f : α → ε) (i : α) (hp : p ≠ 0) :
    eLpNorm f p (dirac i) = ‖f i‖ₑ := by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

lemma enorm_le_eLpNorm_count (f : α → ε) (i : α) (hp : p ≠ 0) :
    ‖f i‖ₑ ≤ eLpNorm f p count := by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ ≤ eLpNorm f p count := eLpNorm_restrict_le ..

lemma eLpNorm_count_lt_top_of_lt [Finite α] (h : ∀ i, ‖f i‖ₑ < ∞) :
    eLpNorm f p .count < ∞ := by
  letI _ := Fintype.ofFinite α
  simp_rw [eLpNorm]
  split_ifs with h2 h3
  · exact ENNReal.zero_lt_top
  · refine (essSup_le_of_ae_le (Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
    · filter_upwards with x
      exact Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ _)
    · simp_rw [Finset.sup_lt_iff ENNReal.zero_lt_top, h, implies_true]
  · refine (ENNReal.rpow_lt_top_iff_of_pos ?_).mpr ?_
    · rw [one_div, inv_pos]
      exact ENNReal.toReal_pos h2 h3
    · simp_rw [lintegral_count, tsum_eq_sum (s := Finset.univ) (by simp), ENNReal.sum_lt_top,
        Finset.mem_univ, forall_const, ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos h2 h3), h,
        implies_true]

lemma eLpNorm_count_lt_top [Finite α] (hp : p ≠ 0) :
    eLpNorm f p .count < ∞ ↔ ∀ i, ‖f i‖ₑ < ∞ :=
  ⟨fun h i ↦ (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

end MeasureTheory
