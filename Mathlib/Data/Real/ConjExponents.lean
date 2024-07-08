/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Real

#align_import data.real.conjugate_exponents from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Real conjugate exponents

This file defines conjugate exponents in `ℝ` and `ℝ≥0`. Real numbers `p` and `q` are *conjugate* if
they are both greater than `1` and satisfy `p⁻¹ + q⁻¹ = 1`. This property shows up often in
analysis, especially when dealing with `L^p` spaces.

## Main declarations

* `Real.IsConjExponent`: Predicate for two real numbers to be conjugate.
* `Real.conjExponent`: Conjugate exponent of a real number.
* `NNReal.IsConjExponent`: Predicate for two nonnegative real numbers to be conjugate.
* `NNReal.conjExponent`: Conjugate exponent of a nonnegative real number.

## TODO

* Eradicate the `1 / p` spelling in lemmas.
* Do we want an `ℝ≥0∞` version?
-/

noncomputable section

open scoped ENNReal

namespace Real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1
#align real.is_conjugate_exponent Real.IsConjExponent

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjExponent (p : ℝ) : ℝ := p / (p - 1)
#align real.conjugate_exponent Real.conjExponent

variable {a b p q : ℝ} (h : p.IsConjExponent q)

namespace IsConjExponent

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
theorem pos : 0 < p := lt_trans zero_lt_one h.one_lt
#align real.is_conjugate_exponent.pos Real.IsConjExponent.pos

theorem nonneg : 0 ≤ p := le_of_lt h.pos
#align real.is_conjugate_exponent.nonneg Real.IsConjExponent.nonneg

theorem ne_zero : p ≠ 0 := ne_of_gt h.pos
#align real.is_conjugate_exponent.ne_zero Real.IsConjExponent.ne_zero

theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.one_lt
#align real.is_conjugate_exponent.sub_one_pos Real.IsConjExponent.sub_one_pos

theorem sub_one_ne_zero : p - 1 ≠ 0 := ne_of_gt h.sub_one_pos
#align real.is_conjugate_exponent.sub_one_ne_zero Real.IsConjExponent.sub_one_ne_zero

protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'

theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
#align real.is_conjugate_exponent.one_div_pos Real.IsConjExponent.one_div_pos

theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
#align real.is_conjugate_exponent.one_div_nonneg Real.IsConjExponent.one_div_nonneg

theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos
#align real.is_conjugate_exponent.one_div_ne_zero Real.IsConjExponent.one_div_ne_zero

theorem conj_eq : q = p / (p - 1) := by
  have := h.inv_add_inv_conj
  rw [← eq_sub_iff_add_eq', inv_eq_iff_eq_inv] at this
  field_simp [this, h.ne_zero]
#align real.is_conjugate_exponent.conj_eq Real.IsConjExponent.conj_eq

lemma conjExponent_eq : conjExponent p = q := h.conj_eq.symm
#align real.is_conjugate_exponent.conjugate_eq Real.IsConjExponent.conjExponent_eq

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add' h.inv_add_inv_conj.symm
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by rw [← h.inv_add_inv_conj, sub_add_cancel_left]

theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq
#align real.is_conjugate_exponent.sub_one_mul_conj Real.IsConjExponent.sub_one_mul_conj

theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj
#align real.is_conjugate_exponent.mul_eq_add Real.IsConjExponent.mul_eq_add

@[symm] protected lemma symm : q.IsConjExponent p where
  one_lt := by simpa only [h.conj_eq] using (one_lt_div h.sub_one_pos).mpr (sub_one_lt p)
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj
#align real.is_conjugate_exponent.symm Real.IsConjExponent.symm

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  rw [h.sub_one_mul_conj]
#align real.is_conjugate_exponent.div_conj_eq_sub_one Real.IsConjExponent.div_conj_eq_sub_one

theorem inv_add_inv_conj_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos h.pos,
    ← ENNReal.ofReal_inv_of_pos h.symm.pos, ← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_conj]
#align real.is_conjugate_exponent.inv_add_inv_conj_ennreal Real.IsConjExponent.inv_add_inv_conj_ennreal

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.IsConjExponent b⁻¹ :=
  ⟨one_lt_inv ha $ by linarith, by simpa only [inv_inv]⟩

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv ha₀ (sub_pos_of_lt ha₁) $ add_tsub_cancel_of_le ha₁.le

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end IsConjExponent

lemma isConjExponent_iff_eq_conjExponent (hp : 1 < p) : p.IsConjExponent q ↔ q = p / (p - 1) :=
  ⟨IsConjExponent.conj_eq, fun h ↦ ⟨hp, by field_simp [h]⟩⟩
#align real.is_conjugate_exponent_iff Real.isConjExponent_iff

lemma IsConjExponent.conjExponent (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff_eq_conjExponent h).2 rfl
#align real.is_conjugate_exponent_conjugate_exponent Real.IsConjExponent.conjExponent

lemma isConjExponent_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).IsConjExponent (1 / b) := by simpa using IsConjExponent.inv_inv ha hb hab
#align real.is_conjugate_exponent_one_div Real.isConjExponent_one_div

end Real

namespace NNReal

/-- Two nonnegative real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ≥0) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1
#align real.is_conjugate_exponent.one_lt_nnreal NNReal.IsConjExponent.one_lt
#align real.is_conjugate_exponent.inv_add_inv_conj_nnreal NNReal.IsConjExponent.inv_add_inv_conj

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
noncomputable def conjExponent (p : ℝ≥0) : ℝ≥0 := p / (p - 1)

variable {a b p q : ℝ≥0} (h : p.IsConjExponent q)

@[simp, norm_cast] lemma isConjExponent_coe : (p : ℝ).IsConjExponent q ↔ p.IsConjExponent q := by
  simp [Real.isConjExponent_iff, isConjExponent_iff]; norm_cast; simp

alias ⟨_, IsConjExponent.coe⟩ := isConjExponent_coe

namespace IsConjExponent

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
lemma one_le : 1 ≤ p := h.one_lt.le
lemma pos : 0 < p := zero_lt_one.trans h.one_lt
lemma ne_zero : p ≠ 0 := h.pos.ne'

lemma sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.one_lt
lemma sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

lemma inv_pos : 0 < p⁻¹ := _root_.inv_pos.2 h.pos
lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add_rev h.inv_add_inv_conj.symm

lemma conj_eq : q = p / (p - 1) := by
  simpa only [← coe_one, ← NNReal.coe_sub h.one_le, ← NNReal.coe_div, coe_inj] using h.coe.conj_eq

lemma conjExponent_eq : conjExponent p = q := h.conj_eq.symm

lemma sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq

lemma mul_eq_add : p * q = p + q := by
  simpa only [← NNReal.coe_mul, ← NNReal.coe_add, NNReal.coe_inj] using h.coe.mul_eq_add

@[symm]
protected lemma symm : q.IsConjExponent p where
  one_lt := by
    rw [h.conj_eq]
    exact (one_lt_div h.sub_one_pos).mpr (tsub_lt_self h.pos zero_lt_one)
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj

lemma div_conj_eq_sub_one : p / q = p - 1 := by field_simp [h.symm.ne_zero]; rw [h.sub_one_mul_conj]

lemma inv_add_inv_conj_ennreal : (p⁻¹ + q⁻¹ : ℝ≥0∞) = 1 := by norm_cast; exact h.inv_add_inv_conj

protected lemma inv_inv (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1) :
    a⁻¹.IsConjExponent b⁻¹ :=
  ⟨one_lt_inv ha.bot_lt $ by rw [← hab]; exact lt_add_of_pos_right _ hb.bot_lt, by
    simpa only [inv_inv] using hab⟩

lemma inv_one_sub_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv ha₀ (tsub_pos_of_lt ha₁).ne' $ add_tsub_cancel_of_le ha₁.le

lemma one_sub_inv_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end IsConjExponent

lemma isConjExponent_iff_eq_conjExponent (h : 1 < p) : p.IsConjExponent q ↔ q = p / (p - 1) := by
  rw [← isConjExponent_coe, Real.isConjExponent_iff_eq_conjExponent (mod_cast h), ← coe_inj,
    NNReal.coe_div, NNReal.coe_sub h.le, coe_one]

protected lemma IsConjExponent.conjExponent (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff_eq_conjExponent h).2 rfl

end NNReal

protected lemma Real.IsConjExponent.toNNReal {p q : ℝ} (hpq : p.IsConjExponent q) :
    p.toNNReal.IsConjExponent q.toNNReal where
  one_lt := by simpa using hpq.one_lt
  inv_add_inv_conj := by rw [← toNNReal_inv, ← toNNReal_inv, ← toNNReal_add hpq.inv_nonneg
    hpq.symm.inv_nonneg, hpq.inv_add_inv_conj, toNNReal_one]
