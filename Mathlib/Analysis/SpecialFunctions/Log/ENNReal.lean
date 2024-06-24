/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.EReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Extended nonnegative real logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.
- `ENNReal.log_orderIso`, `ENNReal.log_equiv`: `log` seen respectively
as an order isomorphism and an homeomorphism.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfy
the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
(with either `y ∈ ℕ` or `y ∈ ℝ`).

## TODO
- Define `exp` on `EReal` and prove its basic properties.

## Tags
ENNReal, EReal, logarithm
-/
namespace ENNReal

open scoped NNReal

section Log

/-! ### Definition -/
section Definition

/-- The logarithm function defined on the extended nonnegative reals `ℝ≥0∞`
to the extended reals `EReal`. Coincides with the usual logarithm function
and with `Real.log` on positive reals, and takes values `log 0 = ⊥` and `log ⊤ = ⊤`.
Conventions about multiplication in `ℝ≥0∞` and addition in `EReal` make the identity
`log (x * y) = log x + log y` unconditional. -/
noncomputable def log (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal
-- noncomputable
-- def log : ℝ≥0∞ → EReal
-- | ∞ => ⊤
-- | x => if x = 0 then ⊥ else Real.log x.toReal


@[simp] lemma log_zero : log 0 = ⊥ := if_pos rfl
@[simp] lemma log_one : log 1 = 0 := by simp [log]
@[simp] lemma log_top : log ⊤ = ⊤ := rfl

@[simp]
lemma log_ofReal (x : ℝ) : log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x) := by
  simp only [log, ENNReal.none_eq_top, ENNReal.ofReal_ne_top, IsEmpty.forall_iff,
    ENNReal.ofReal_eq_zero, EReal.coe_ennreal_ofReal]
  split_ifs with h_nonpos
  · rfl
  · trivial
  · rw [ENNReal.toReal_ofReal]
    exact (not_le.mp h_nonpos).le

lemma log_ofReal_of_pos {x : ℝ} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.log x := by
  rw [log_ofReal, if_neg]
  exact not_le.mpr hx

theorem log_pos_real {x : ℝ≥0∞} (h : x ≠ 0) (h' : x ≠ ⊤) :
    log x = Real.log (ENNReal.toReal x) := by simp [log, h, h']

theorem log_pos_real' {x : ℝ≥0∞} (h : 0 < x.toReal) :
    log x = Real.log (ENNReal.toReal x) := by
  simp [log, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 h).1),
    ne_of_lt (ENNReal.toReal_pos_iff.1 h).2]

theorem log_of_nnreal {x : ℝ≥0} (h : x ≠ 0) :
    log (x : ℝ≥0∞) = Real.log x := by simp [log, h]

end Definition

/-! ### Monotonicity -/
section Monotonicity

theorem log_strictMono : StrictMono log := by
  intro x y h
  unfold log
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · exfalso; exact lt_irrefl 0 h
    · simp
    · simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1),
      ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.bot_lt_coe]
  · exfalso; exact (ne_top_of_lt h) (Eq.refl ⊤)
  · simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1),
      ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · exfalso; rw [← ENNReal.bot_eq_zero] at h; exact not_lt_bot h
    · simp
    · simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1), ↓reduceIte,
        ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.coe_lt_coe_iff]
      apply Real.log_lt_log x_real
      exact (ENNReal.toReal_lt_toReal (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2)
        (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2)).2 h

theorem log_monotone : Monotone log := log_strictMono.monotone

theorem log_injective : Function.Injective log := log_strictMono.injective

theorem log_surjective : Function.Surjective log := by
  intro y
  cases' eq_bot_or_bot_lt y with y_bot y_nbot
  · exact y_bot ▸ ⟨⊥, log_zero⟩
  cases' eq_top_or_lt_top y with y_top y_ntop
  · exact y_top ▸ ⟨⊤, log_top⟩
  use ENNReal.ofReal (Real.exp y.toReal)
  have exp_y_pos := not_le_of_lt (Real.exp_pos y.toReal)
  simp only [log, ofReal_eq_zero, exp_y_pos, ↓reduceIte, ofReal_ne_top,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos y.toReal)), Real.log_exp y.toReal]
  exact EReal.coe_toReal (ne_of_lt y_ntop) (Ne.symm (ne_of_lt y_nbot))

theorem log_bijective : Function.Bijective log := ⟨log_injective, log_surjective⟩

-- /-- `log` as an order isomorphism. -/
-- noncomputable def log_orderIso : ℝ≥0∞ ≃o EReal :=
--   StrictMono.orderIsoOfSurjective log log_strictMono log_surjective

-- @[simp] lemma log_orderIso_apply (x : ℝ≥0∞) : log_orderIso x = log x := rfl

@[simp]
theorem log_eq_iff {x y : ℝ≥0∞} : log x = log y ↔ x = y :=
  Iff.intro (@log_injective x y) (fun h ↦ by rw [h])

@[simp]
theorem log_eq_bot_iff {x : ℝ≥0∞} : log x = ⊥ ↔ x = 0 := log_zero ▸ @log_eq_iff x 0

@[simp]
theorem log_eq_one_iff {x : ℝ≥0∞} : log x = 0 ↔ x = 1 := log_one ▸ @log_eq_iff x 1

@[simp]
theorem log_eq_top_iff {x : ℝ≥0∞} : log x = ⊤ ↔ x = ⊤ := log_top ▸ @log_eq_iff x ⊤

-- @[simp]
-- theorem log_lt_iff_lt {x y : ℝ≥0∞} : log x < log y ↔ x < y := OrderIso.lt_iff_lt log_orderIso

-- @[simp]
-- theorem log_bot_lt_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_iff_lt 0 x

-- @[simp]
-- theorem log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_iff_lt x ⊤

-- @[simp]
-- theorem log_lt_one_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_iff_lt x 1

-- @[simp]
-- theorem log_one_lt_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_iff_lt 1 x

-- @[simp]
-- theorem log_le_iff_le {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := OrderIso.le_iff_le log_orderIso

-- @[simp]
-- theorem log_le_one_iff {x : ℝ≥0∞} : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_iff_le x 1

-- @[simp]
-- theorem log_one_le_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_iff_le 1 x

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

theorem log_mul_add {x y : ℝ≥0∞} : log (x * y) = log x + log y := by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1)
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1)]
    · have xy_real := Real.mul_pos x_real y_real
      rw [← ENNReal.toReal_mul] at xy_real
      rw_mod_cast [log_pos_real' xy_real, log_pos_real' y_real, ENNReal.toReal_mul]
      exact Real.log_mul (Ne.symm (ne_of_lt x_real)) (Ne.symm (ne_of_lt y_real))

theorem log_pow {x : ℝ≥0∞} {n : ℕ} : log (x ^ n) = (n : ℝ≥0∞) * log x := by
  cases' Nat.eq_zero_or_pos n with n_zero n_pos
  · simp [n_zero, pow_zero x]
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · rw [zero_pow (Ne.symm (ne_of_lt n_pos)), log_zero, EReal.mul_bot_of_pos]; norm_cast
  · rw [ENNReal.top_pow n_pos, log_top, EReal.mul_top_of_pos]; norm_cast
  · replace x_real := ENNReal.toReal_pos_iff.1 x_real
    have x_ne_zero := Ne.symm (LT.lt.ne x_real.1)
    have x_ne_top := LT.lt.ne x_real.2
    simp only [log, pow_eq_zero_iff', x_ne_zero, ne_eq, false_and, ↓reduceIte, pow_eq_top_iff,
      x_ne_top, toReal_pow, Real.log_pow, EReal.coe_mul]
    rfl

theorem log_rpow {x : ℝ≥0∞} {y : ℝ} : log (x ^ y) = y * log x := by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_lt y_neg, ne_of_lt y_neg, log_top, log_zero]
      exact Eq.symm (EReal.coe_mul_bot_of_neg y_neg)
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top]
      exact Eq.symm (EReal.coe_mul_top_of_neg y_neg)
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y

lemma log_inv {x : ℝ≥0∞} : log x⁻¹ = - log x := by
  simp [← rpow_neg_one, log_rpow]

end Morphism

end Log

section Exp

/-- Exponential as a function from `EReal` to `ℝ≥0∞`. -/
noncomputable
def exp : EReal → ℝ≥0∞
| ⊥ => 0
| ⊤ => ∞
| (x : ℝ) => ENNReal.ofReal (Real.exp x)

@[simp] lemma exp_bot : exp ⊥ = 0 := rfl
@[simp] lemma exp_top : exp ⊤ = ∞ := rfl

@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := rfl

@[simp] lemma exp_eq_zero_iff {x : EReal} : exp x = 0 ↔ x = ⊥ := by
  induction' x using EReal.rec with x <;> simp [Real.exp_pos]

@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction' x using EReal.rec with x <;> simp

lemma exp_strictMono : StrictMono exp := by
  intro x y h
  induction' x using EReal.rec with x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction' y using EReal.rec with y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_lt_exp_of_lt (mod_cast h), Real.exp_pos y⟩
    · simp
  · exact (not_top_lt h).elim

lemma exp_monotone : Monotone exp := by
  intro x y h
  induction' x using EReal.rec with x
  · simp
  · induction' y using EReal.rec with y
    · simp at h
    · rw [exp_coe, exp_coe]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le (mod_cast h))
    · simp
  · rw [top_le_iff] at h
    simp [h.symm, exp_top, top_le_iff]

lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction' x using EReal.rec with x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction' x using EReal.rec with x
  · simp
  · induction' y using EReal.rec with y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction' y using EReal.rec with y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

end Exp

section LogExp

@[simp] lemma log_exp (x : EReal) : log (exp x) = x := by
  induction' x using EReal.rec with x
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

@[simp]
theorem log_lt_iff_lt {x y : ℝ≥0∞} : log x < log y ↔ x < y := by
  refine ⟨fun h ↦ ?_, fun h ↦ log_strictMono h⟩
  rw [← exp_log x, ← exp_log y]
  exact exp_strictMono h

@[simp]
theorem log_bot_lt_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_iff_lt 0 x

@[simp]
theorem log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_iff_lt x ⊤

@[simp]
theorem log_lt_one_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_iff_lt x 1

@[simp]
theorem log_one_lt_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_iff_lt 1 x

@[simp]
theorem log_le_iff_le {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ log_monotone h⟩
  rw [← exp_log x, ← exp_log y]
  exact exp_monotone h

@[simp]
theorem log_le_one_iff {x : ℝ≥0∞} : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_iff_le x 1

@[simp]
theorem log_one_le_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_iff_le 1 x

@[simp]
lemma exp_le_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b := by
  conv_rhs => rw [← log_exp a, ← log_exp b, log_le_iff_le]

/-- `ENNReal.log` and its inverse `ENNReal.exp` are an order isomorphism between `ℝ≥0∞` and `EReal`. -/
noncomputable
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_iff_le, forall_const]

@[simp] lemma logOrderIso_apply (x : ℝ≥0∞) : logOrderIso x = log x := rfl
@[simp] lemma logOrderIso_symm_apply (x : EReal) : logOrderIso.symm x = exp x := rfl

/-! ### Topological properties -/

section Continuity

/-- `log` as a homeomorphism. -/
noncomputable def log_homeomorph : ℝ≥0∞ ≃ₜ EReal := logOrderIso.toHomeomorph

@[simp] theorem log_homeomorph_apply (x : ℝ≥0∞) : log_homeomorph x = log x := rfl

/-- `exp` as a homeomorphism. -/
noncomputable def exp_homeomorph : EReal ≃ₜ ℝ≥0∞ := logOrderIso.symm.toHomeomorph

@[simp] theorem exp_homeomorph_apply (x : EReal) : exp_homeomorph x = exp x := rfl

@[continuity, fun_prop]
lemma continuous_log : Continuous log := logOrderIso.continuous

@[continuity, fun_prop]
lemma continuous_exp : Continuous exp := logOrderIso.symm.continuous

end Continuity

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

end LogExp

end ENNReal

instance : TopologicalSpace.MetrizableSpace EReal :=
  ENNReal.logOrderIso.symm.toHomeomorph.embedding.metrizableSpace
