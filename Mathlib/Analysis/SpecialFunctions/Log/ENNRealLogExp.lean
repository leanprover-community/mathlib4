/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish

/-!
# Properties of the extended logarithm and exponential

We prove that `log` and `exp` define order isomorphisms between `ℝ≥0∞` and `EReal`.
## Main Definitions
- `ENNReal.logOrderIso`: The order isomorphism between `ℝ≥0∞` and `EReal` defined by `log`
and `exp`.
- `ENNReal.logHomeomorph`: `log` as a homeomorphism.
- `EReal.expHomeomorph`: `exp` as a homeomorphism.

## Main Results
- `ENNReal.log_exp`, `ENNReal.exp_log`: `log` and `exp` are inverses of each other.
- `ENNReal.exp_nmul`, `ENNReal.exp_mul`: `exp` satisfies the identities `exp (n * x) = (exp x) ^ n`
and `exp (x * y) = (exp x) ^ y`.
- `instMetrizableSpaceEReal`: `EReal` is a metrizable space.

## Tags
ENNReal, EReal, logarithm, exponential
-/

open EReal ENNReal
section LogExp
namespace EReal

@[simp] lemma log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

end EReal

namespace ENNReal
@[simp] lemma exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]

end ENNReal
end LogExp

section Log
namespace ENNReal

@[simp]
lemma log_lt_log_iff {x y : ℝ≥0∞} : log x < log y ↔ x < y := by
  refine ⟨fun h ↦ ?_, fun h ↦ log_strictMono h⟩
  rw [← exp_log x, ← exp_log y]
  exact exp_strictMono h

@[simp] lemma bot_lt_log_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_log_iff 0 x

@[simp] lemma log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_log_iff x ⊤

@[simp] lemma log_lt_zero_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_log_iff x 1

@[simp] lemma zero_lt_log_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_log_iff 1 x

@[simp]
lemma log_le_log_iff {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ log_monotone h⟩
  rw [← exp_log x, ← exp_log y]
  exact exp_monotone h

@[simp] lemma log_le_zero_iff {x : ℝ≥0∞} : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_log_iff x 1

@[simp] lemma zero_le_log_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_log_iff 1 x

end ENNReal
end Log

section Exp
namespace EReal
@[simp]
lemma exp_lt_exp_iff {a b : EReal} : exp a < exp b ↔ a < b := by
  conv_rhs => rw [← log_exp a, ← log_exp b, log_lt_log_iff]

@[simp] lemma zero_lt_exp_iff {a : EReal} : 0 < exp a ↔ ⊥ < a := exp_bot ▸ @exp_lt_exp_iff ⊥ a

@[simp] lemma exp_lt_top_iff {a : EReal} : exp a < ⊤ ↔ a < ⊤ := exp_top ▸ @exp_lt_exp_iff a ⊤

@[simp] lemma exp_lt_one_iff {a : EReal} : exp a < 1 ↔ a < 0 := exp_zero ▸ @exp_lt_exp_iff a 0

@[simp] lemma one_lt_exp_iff {a : EReal} : 1 < exp a ↔ 0 < a := exp_zero ▸ @exp_lt_exp_iff 0 a

@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b := by
  conv_rhs => rw [← log_exp a, ← log_exp b, log_le_log_iff]

@[simp] lemma exp_le_one_iff {a : EReal} : exp a ≤ 1 ↔ a ≤ 0 := exp_zero ▸ @exp_le_exp_iff a 0

@[simp] lemma one_le_exp_iff {a : EReal} : 1 ≤ exp a ↔ 0 ≤ a := exp_zero ▸ @exp_le_exp_iff 0 a

lemma exp_nmul (x : EReal) (n : ℕ) : exp (n * x) = (exp x) ^ n := by
  simp_rw [← log_eq_iff, log_pow, log_exp]
  norm_cast

lemma exp_mul (x : EReal) (y : ℝ) : exp (x * y) = (exp x) ^ y := by
  rw [← log_eq_iff, log_rpow, log_exp, log_exp, mul_comm]

end EReal
end Exp

namespace ENNReal
section OrderIso

/-- `ENNReal.log` and its inverse `ENNReal.exp` are an order isomorphism between `ℝ≥0∞` and
`EReal`. -/
noncomputable
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]

@[simp] lemma logOrderIso_apply (x : ℝ≥0∞) : logOrderIso x = log x := rfl
@[simp] lemma logOrderIso_symm_apply (x : EReal) : logOrderIso.symm x = exp x := rfl

end OrderIso

section Continuity

/-- `log` as a homeomorphism. -/
noncomputable def logHomeomorph : ℝ≥0∞ ≃ₜ EReal := logOrderIso.toHomeomorph

@[simp] lemma logHomeomorph_apply (x : ℝ≥0∞) : logHomeomorph x = log x := rfl

/-- `exp` as a homeomorphism. -/
noncomputable def _root_.EReal.expHomeomorph : EReal ≃ₜ ℝ≥0∞ := logOrderIso.symm.toHomeomorph

@[simp] lemma _root_.EReal.expHomeomorph_apply (x : EReal) : expHomeomorph x = exp x := rfl

@[simp] lemma logHomeomorph_symm : logHomeomorph.symm = expHomeomorph := rfl

@[simp] lemma _root_.EReal.expHomeomorph_symm : expHomeomorph.symm = logHomeomorph := rfl

@[continuity, fun_prop]
lemma continuous_log : Continuous log := logOrderIso.continuous

@[continuity, fun_prop]
lemma continuous_exp : Continuous exp := logOrderIso.symm.continuous

end Continuity

section Measurability

@[measurability, fun_prop]
lemma measurable_log : Measurable log := continuous_log.measurable

@[measurability, fun_prop]
lemma measurable_exp : Measurable exp := continuous_exp.measurable

@[measurability, fun_prop]
lemma _root_.Measurable.ereal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ log (f x) := measurable_log.comp hf

@[measurability, fun_prop]
lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x ↦ exp (f x) := measurable_exp.comp hf

end Measurability

end ENNReal

instance : TopologicalSpace.MetrizableSpace EReal :=
  ENNReal.logOrderIso.symm.toHomeomorph.embedding.metrizableSpace

instance : PolishSpace ENNReal :=
  ClosedEmbedding.polishSpace ⟨ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.embedding,
    ENNReal.orderIsoUnitIntervalBirational.range_eq ▸ isClosed_univ⟩

instance : PolishSpace EReal :=
  ClosedEmbedding.polishSpace ⟨ENNReal.logOrderIso.symm.toHomeomorph.embedding,
    ENNReal.logOrderIso.symm.toHomeomorph.range_coe ▸ isClosed_univ⟩
