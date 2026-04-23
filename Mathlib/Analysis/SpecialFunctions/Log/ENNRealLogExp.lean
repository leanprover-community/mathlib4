/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Order.MonotoneContinuity
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
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
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
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Properties of the extended logarithm and exponential

We prove that `log` and `exp` define order isomorphisms between `ℝ≥0∞` and `EReal`.

## Main Definitions
- `ENNReal.logOrderIso`: The order isomorphism between `ℝ≥0∞` and `EReal` defined by `log`
  and `exp`.
- `EReal.expOrderIso`: The order isomorphism between `EReal` and `ℝ≥0∞` defined by `exp`
  and `log`.
- `ENNReal.logHomeomorph`: `log` as a homeomorphism.
- `EReal.expHomeomorph`: `exp` as a homeomorphism.

## Main Results
- `EReal.log_exp`, `ENNReal.exp_log`: `log` and `exp` are inverses of each other.
- `EReal.exp_nmul`, `EReal.exp_mul`: `exp` satisfies the identities `exp (n * x) = (exp x) ^ n`
  and `exp (x * y) = (exp x) ^ y`.
- `EReal` is a Polish space.

## Tags
ENNReal, EReal, logarithm, exponential
-/

@[expose] public section

open EReal ENNReal Topology
section LogExp

@[simp] lemma EReal.log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

@[simp] lemma ENNReal.exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]

end LogExp

section Exp
namespace EReal

lemma exp_nmul (x : EReal) (n : ℕ) : exp (n * x) = (exp x) ^ n := by
  simp_rw [← log_eq_iff, log_pow, log_exp]

lemma exp_mul (x : EReal) (y : ℝ) : exp (x * y) = (exp x) ^ y := by
  rw [← log_eq_iff, log_rpow, log_exp, log_exp, mul_comm]

lemma ENNReal.rpow_eq_exp_mul_log (x : ℝ≥0∞) (y : ℝ) : x ^ y = exp (y * log x) := by
  rw [mul_comm, EReal.exp_mul, exp_log]

end EReal
end Exp

namespace ENNReal
section OrderIso

/-- `ENNReal.log` and its inverse `EReal.exp` are an order isomorphism between `ℝ≥0∞` and
`EReal`. -/
noncomputable
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]

@[simp] lemma logOrderIso_apply (x : ℝ≥0∞) : logOrderIso x = log x := rfl

/-- `EReal.exp` and its inverse `ENNReal.log` are an order isomorphism between `EReal` and
`ℝ≥0∞`. -/
noncomputable
def _root_.EReal.expOrderIso := logOrderIso.symm

@[simp] lemma _root_.EReal.expOrderIso_apply (x : EReal) : expOrderIso x = exp x := rfl

@[simp] lemma logOrderIso_symm : logOrderIso.symm = expOrderIso := rfl
@[simp] lemma _root_.EReal.expOrderIso_symm : expOrderIso.symm = logOrderIso := rfl

end OrderIso

section Continuity

/-- `log` as a homeomorphism. -/
noncomputable def logHomeomorph : ℝ≥0∞ ≃ₜ EReal := logOrderIso.toHomeomorph

@[simp] lemma logHomeomorph_apply (x : ℝ≥0∞) : logHomeomorph x = log x := rfl

/-- `exp` as a homeomorphism. -/
noncomputable def _root_.EReal.expHomeomorph : EReal ≃ₜ ℝ≥0∞ := expOrderIso.toHomeomorph

@[simp] lemma _root_.EReal.expHomeomorph_apply (x : EReal) : expHomeomorph x = exp x := rfl

@[simp] lemma logHomeomorph_symm : logHomeomorph.symm = expHomeomorph := rfl

@[simp] lemma _root_.EReal.expHomeomorph_symm : expHomeomorph.symm = logHomeomorph := rfl

@[continuity, fun_prop]
lemma continuous_log : Continuous log := logOrderIso.continuous

@[continuity, fun_prop]
lemma continuous_exp : Continuous exp := expOrderIso.continuous

lemma _root_.EReal.tendsto_exp_nhds_top_nhds_top : Filter.Tendsto exp (𝓝 ⊤) (𝓝 ⊤) :=
  continuous_exp.tendsto ⊤

lemma _root_.EReal.tendsto_exp_nhds_zero_nhds_one : Filter.Tendsto exp (𝓝 0) (𝓝 1) := by
  convert continuous_exp.tendsto 0
  simp

lemma _root_.EReal.tendsto_exp_nhds_bot_nhds_zero : Filter.Tendsto exp (𝓝 ⊥) (𝓝 0) :=
  continuous_exp.tendsto ⊥

lemma tendsto_rpow_atTop_of_one_lt_base {b : ℝ≥0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atTop (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

lemma tendsto_rpow_atTop_of_base_lt_one {b : ℝ≥0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atTop (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

lemma tendsto_rpow_atBot_of_one_lt_base {b : ℝ≥0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atBot (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp

lemma tendsto_rpow_atBot_of_base_lt_one {b : ℝ≥0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atBot (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

end Continuity

section Measurability

@[fun_prop]
lemma measurable_log : Measurable log := continuous_log.measurable

@[fun_prop]
lemma _root_.EReal.measurable_exp : Measurable exp := continuous_exp.measurable

@[fun_prop]
lemma _root_.Measurable.ennreal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ log (f x) := measurable_log.comp hf

@[fun_prop]
lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x ↦ exp (f x) := measurable_exp.comp hf

end Measurability

end ENNReal

instance : PolishSpace EReal := ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace
