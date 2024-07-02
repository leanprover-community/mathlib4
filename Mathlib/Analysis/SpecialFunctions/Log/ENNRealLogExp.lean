/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealExp
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
- `EReal.exp_homeomorph`: `exp` as a homeomorphism.

## Main Results
- `ENNReal.log_exp`, `ENNReal.exp_log`: `log` and `exp` are inverses of each other.
- `ENNReal.exp_nmul`, `ENNReal.exp_mul`: `exp` satisfies the identities `exp (n * x) = (exp x) ^ n`
and `exp (x * y) = (exp x) ^ y`.
- `instMetrizableSpaceEReal`: `EReal` is a metrizable space.

## Tags
ENNReal, EReal, logarithm, exponential
-/
namespace ENNReal

open scoped NNReal

section LogExp

@[simp] lemma log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp

@[simp] lemma exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]

end LogExp

section Log

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

end Log

section Exp

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

end Exp

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

@[simp] lemma log_homeomorph_apply (x : ℝ≥0∞) : logHomeomorph x = log x := rfl

/-- `exp` as a homeomorphism. -/
noncomputable def _root_.EReal.exp_homeomorph : EReal ≃ₜ ℝ≥0∞ := logOrderIso.symm.toHomeomorph

@[simp] lemma _root_.EReal.exp_homeomorph_apply (x : EReal) : EReal.exp_homeomorph x = exp x := rfl

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

noncomputable
instance : EDist EReal where
  edist
    | ⊥, ⊥ | ⊤, ⊤ => 0
    | ⊥, ⊤ | ⊤, ⊥ => ⊤
    | ⊥, (y : ℝ) | ⊤, (y : ℝ) | (x : ℝ), ⊤ | (x : ℝ), ⊥ => ⊤
    | (x : ℝ), (y : ℝ) => ENNReal.ofReal (dist x y)

lemma EReal.eDist_self (x : EReal) : edist x x = 0 := by
  induction x with
  | h_top | h_bot => rfl
  | h_real x =>
    change ENNReal.ofReal (dist x x) = 0
    exact dist_self x ▸ ENNReal.ofReal_zero

lemma EReal.eDist_comm (x y : EReal) : edist x y = edist y x := by
  induction x <;> induction y <;>
    try { rfl }
  change ENNReal.ofReal (dist _ _) = ENNReal.ofReal (dist _ _)
  rw [dist_comm]

@[simp]
lemma EReal.eDist_coe_top (x : ℝ) : edist (x : EReal) ⊤ = ⊤ := rfl

@[simp]
lemma EReal.eDist_top_coe (x : ℝ) : edist ⊤ (x : EReal) = ⊤ := rfl

@[simp]
lemma EReal.eDist_bot_coe (x : ℝ) : edist ⊥ (x : EReal) = ⊤ := rfl

@[simp]
lemma EReal.eDist_coe_bot (x : ℝ) : edist (x : EReal) ⊥ = ⊤ := rfl

@[simp]
lemma EReal.eDist_coe_coe (x y : ℝ) :
    edist (x : EReal) (y : EReal) = ENNReal.ofReal (dist x y) := rfl

@[simp]
lemma EReal.eDist_top_bot : edist (⊤ : EReal) ⊥  = ⊤ := rfl

@[simp]
lemma EReal.eDist_bot_top : edist (⊥ : EReal) ⊤ = ⊤ := rfl

noncomputable
instance : PseudoEMetricSpace EReal where
  edist := EDist.edist
  edist_self := EReal.eDist_self
  edist_comm := EReal.eDist_comm
  edist_triangle x y z := by
    induction x <;> induction y <;> induction z <;>
      try { simp [EReal.eDist_self, EReal.eDist_coe_top, EReal.eDist_coe_bot, EReal.eDist_top_coe,
        EReal.eDist_bot_coe] }
    simp_rw [EReal.eDist_coe_coe, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
    exact ENNReal.ofReal_le_ofReal (dist_triangle _ _ _)

noncomputable
instance : EMetricSpace EReal where
  __ := instPseudoEMetricSpaceEReal
  eq_of_edist_eq_zero h := by
    rename_i x y
    induction x <;> induction y <;> simp_all

noncomputable
instance : UniformSpace EReal := by exact PseudoEMetricSpace.toUniformSpace

instance : (uniformity EReal).IsCountablyGenerated := EMetric.instIsCountablyGeneratedUniformity (α := EReal)

instance : UniformSpace EReal := uniformSpaceOfCompactT2

instance : PolishSpace EReal := by
  --after solving the last sorry this can probably be replaced with a proof term
  convert PolishSpace.of_separableSpace_completeSpace_metrizable
  · infer_instance
  · infer_instance
  · convert EMetric.instIsCountablyGeneratedUniformity (α := EReal)
    sorry
  · infer_instance
