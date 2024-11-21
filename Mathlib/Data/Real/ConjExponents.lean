/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Real

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
* `ENNReal.IsConjExponent`: Predicate for two extended nonnegative real numbers to be conjugate.
* `ENNReal.conjExponent`: Conjugate exponent of an extended nonnegative real number.

## TODO

* Eradicate the `1 / p` spelling in lemmas.
* Do we want an `ℝ≥0∞` version?
-/

noncomputable section

open scoped ENNReal NNReal

namespace Real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjExponent (p : ℝ) : ℝ := p / (p - 1)

variable {a b p q : ℝ} (h : p.IsConjExponent q)

namespace IsConjExponent

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/

section
include h

theorem pos : 0 < p := lt_trans zero_lt_one h.one_lt

theorem nonneg : 0 ≤ p := le_of_lt h.pos

theorem ne_zero : p ≠ 0 := ne_of_gt h.pos

theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.one_lt

theorem sub_one_ne_zero : p - 1 ≠ 0 := ne_of_gt h.sub_one_pos

protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'

theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos

theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos

theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

theorem conj_eq : q = p / (p - 1) := by
  have := h.inv_add_inv_conj
  rw [← eq_sub_iff_add_eq', inv_eq_iff_eq_inv] at this
  field_simp [this, h.ne_zero]

lemma conjExponent_eq : conjExponent p = q := h.conj_eq.symm

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add' h.inv_add_inv_conj.symm
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by rw [← h.inv_add_inv_conj, sub_add_cancel_left]

theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq

theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

@[symm] protected lemma symm : q.IsConjExponent p where
  one_lt := by simpa only [h.conj_eq] using (one_lt_div h.sub_one_pos).mpr (sub_one_lt p)
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  rw [h.sub_one_mul_conj]

theorem inv_add_inv_conj_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos h.pos,
    ← ENNReal.ofReal_inv_of_pos h.symm.pos, ← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_conj]

end

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.IsConjExponent b⁻¹ :=
  ⟨(one_lt_inv₀ ha).2 <| by linarith, by simpa only [inv_inv]⟩

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv ha₀ (sub_pos_of_lt ha₁) <| add_tsub_cancel_of_le ha₁.le

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end IsConjExponent

lemma isConjExponent_comm : p.IsConjExponent q ↔ q.IsConjExponent p := ⟨.symm, .symm⟩

lemma isConjExponent_iff_eq_conjExponent (hp : 1 < p) : p.IsConjExponent q ↔ q = p / (p - 1) :=
  ⟨IsConjExponent.conj_eq, fun h ↦ ⟨hp, by field_simp [h]⟩⟩

lemma IsConjExponent.conjExponent (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff_eq_conjExponent h).2 rfl

lemma isConjExponent_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).IsConjExponent (1 / b) := by simpa using IsConjExponent.inv_inv ha hb hab

end Real

namespace NNReal

/-- Two nonnegative real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ≥0) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

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

section
include h

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

end

protected lemma inv_inv (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1) :
    a⁻¹.IsConjExponent b⁻¹ :=
  ⟨(one_lt_inv₀ ha.bot_lt).2 <| by rw [← hab]; exact lt_add_of_pos_right _ hb.bot_lt, by
    simpa only [inv_inv] using hab⟩

lemma inv_one_sub_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv ha₀ (tsub_pos_of_lt ha₁).ne' <| add_tsub_cancel_of_le ha₁.le

lemma one_sub_inv_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end IsConjExponent

lemma isConjExponent_comm : p.IsConjExponent q ↔ q.IsConjExponent p := ⟨.symm, .symm⟩

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

namespace ENNReal

/-- Two extended nonnegative real exponents `p, q` are conjugate and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. Note that we permit one of the exponents to be `∞` and the other `1`. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ≥0∞) : Prop where
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

/-- The conjugate exponent of `p` is `q = 1 + (p - 1)⁻¹`, so that `1/p + 1/q = 1`. -/
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := 1 + (p - 1)⁻¹

lemma coe_conjExponent {p : ℝ≥0} (hp : 1 < p) : p.conjExponent = conjExponent p := by
  rw [NNReal.conjExponent, conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]

variable {a b p q : ℝ≥0∞} (h : p.IsConjExponent q)

@[simp, norm_cast] lemma isConjExponent_coe {p q : ℝ≥0} :
    IsConjExponent p q ↔ p.IsConjExponent q := by
  simp only [isConjExponent_iff, NNReal.isConjExponent_iff]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · simpa using (ENNReal.lt_add_right (fun hp ↦ by simp [hp] at h) <| by simp).trans_eq h
  · rw [← coe_inv, ← coe_inv] at h
    · norm_cast at h
    all_goals rintro rfl; simp at h
  · rintro ⟨hp, h⟩
    rw [← coe_inv (zero_lt_one.trans hp).ne', ← coe_inv, ← coe_add, h, coe_one]
    rintro rfl
    simp [hp.ne'] at h

alias ⟨_, _root_.NNReal.IsConjExponent.coe_ennreal⟩ := isConjExponent_coe

namespace IsConjExponent

protected lemma conjExponent (hp : 1 ≤ p) : p.IsConjExponent (conjExponent p) := by
  have : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [isConjExponent_iff, conjExponent, add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := ℝ≥0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp [tsub_eq_zero_of_le]
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div, ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp), one_div]
    _ = (1 - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le, ← inv_eq_iff_eq_inv, div_eq_mul_inv, ENNReal.mul_inv, inv_inv,
        ENNReal.mul_sub, ENNReal.inv_mul_cancel, mul_one] <;> simp [*]

section
include h

@[symm]
protected lemma symm : q.IsConjExponent p where
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj

lemma one_le : 1 ≤ p := ENNReal.inv_le_one.1 <| by
  rw [← add_zero p⁻¹, ← h.inv_add_inv_conj]; gcongr; positivity

lemma pos : 0 < p := zero_lt_one.trans_le h.one_le
lemma ne_zero : p ≠ 0 := h.pos.ne'

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ :=
  ENNReal.sub_eq_of_eq_add_rev' one_ne_top h.inv_add_inv_conj.symm

lemma conjExponent_eq : conjExponent p = q := by
  have hp : 1 ≤ p := h.one_le
  have : p⁻¹ ≠ ∞ := by simpa using h.ne_zero
  simpa [ENNReal.add_right_inj, *] using
    (IsConjExponent.conjExponent hp).inv_add_inv_conj.trans h.inv_add_inv_conj.symm

lemma conj_eq : q = 1 + (p - 1)⁻¹ := h.conjExponent_eq.symm

lemma mul_eq_add : p * q = p + q := by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [h.symm.ne_zero]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [h.ne_zero]
  rw [← mul_one (_ * _), ← h.inv_add_inv_conj, mul_add, mul_right_comm,
    ENNReal.mul_inv_cancel h.ne_zero hp, one_mul, mul_assoc,
    ENNReal.mul_inv_cancel h.symm.ne_zero hq, mul_one, add_comm]

lemma div_conj_eq_sub_one : p / q = p - 1 := by
  obtain rfl | hq := eq_or_ne q ∞
  · simp [h.symm.conj_eq, tsub_eq_zero_of_le]
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self h.symm.ne_zero hq, ← ENNReal.add_div, ← h.mul_eq_add, mul_div_assoc,
    ENNReal.div_self h.symm.ne_zero hq, mul_one]

end

protected lemma inv_inv (hab : a + b = 1) : a⁻¹.IsConjExponent b⁻¹ where
  inv_add_inv_conj := by simpa only [inv_inv] using hab

lemma inv_one_sub_inv (ha : a ≤ 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv <| add_tsub_cancel_of_le ha

lemma one_sub_inv_inv (ha : a ≤ 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ := (inv_one_sub_inv ha).symm

lemma top_one : IsConjExponent ∞ 1 := ⟨by simp⟩
lemma one_top : IsConjExponent 1 ∞ := ⟨by simp⟩

end IsConjExponent

lemma isConjExponent_comm : p.IsConjExponent q ↔ q.IsConjExponent p := ⟨.symm, .symm⟩

lemma isConjExponent_iff_eq_conjExponent (hp : 1 ≤ p) : p.IsConjExponent q ↔ q = 1 + (p - 1)⁻¹ :=
  ⟨fun h ↦ h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

end ENNReal
