/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Operations

/-!
# Results about division in extended non-negative reals

This file establishes basic properties related to the inversion and division operations on `ℝ≥0∞`.
For instance, as a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation
with integer exponent.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

assert_not_exists Finset

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

@[simp] theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show sInf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp

@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le <| by
    simp [*, h.ne', top_mul]

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <| sInf_le <| mem_setOf.2 <| by rw [← coe_mul, mul_inv_cancel₀ hr, coe_one]

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

lemma coe_div_le : ↑(p / r) ≤ (p / r : ℝ≥0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using mul_le_mul_left' coe_inv_le _

theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]

instance : DivInvOneMonoid ℝ≥0∞ :=
  { inferInstanceAs (DivInvMonoid ℝ≥0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℝ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel₀ h0

protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht

/-- See `ENNReal.inv_mul_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma inv_mul_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_left'` for a stronger version. -/
protected lemma inv_mul_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a⁻¹ * (a * b) = b :=
  ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma mul_inv_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_left'` for a stronger version. -/
protected lemma mul_inv_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (a⁻¹ * b) = b :=
  ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma mul_inv_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_right'` for a stronger version. -/
protected lemma mul_inv_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b * b⁻¹ = a :=
  ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.inv_mul_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma inv_mul_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_right'` for a stronger version. -/
protected lemma inv_mul_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b⁻¹ * b = a :=
  ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.mul_div_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma mul_div_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b / b = a := ENNReal.mul_inv_cancel_right' hb₀ hb

/-- See `ENNReal.mul_div_cancel_right'` for a stronger version. -/
protected lemma mul_div_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b / b = a :=
  ENNReal.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.div_mul_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma div_mul_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : b / a * a = b :=
  ENNReal.inv_mul_cancel_right' ha₀ ha

/-- See `ENNReal.div_mul_cancel'` for a stronger version. -/
protected lemma div_mul_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : b / a * a = b :=
  ENNReal.div_mul_cancel' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma mul_div_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : a * (b / a) = b := by
  rw [mul_comm, ENNReal.div_mul_cancel' ha₀ ha]

/-- See `ENNReal.mul_div_cancel'` for a stronger version. -/
protected lemma mul_div_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (b / a) = b :=
  ENNReal.mul_div_cancel' (by simp [ha₀]) (by simp [ha])

protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]

protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]

instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]

@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
theorem div_ne_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y ≠ ∞ := (div_lt_top h1 h2).ne

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
  ENNReal.mul_pos ha <| ENNReal.inv_ne_zero.2 hb

protected theorem inv_mul_le_iff {x y z : ℝ≥0∞} (h1 : x ≠ 0) (h2 : x ≠ ∞) :
    x⁻¹ * y ≤ z ↔ y ≤ x * z := by
  rw [← mul_le_mul_left h1 h2, ← mul_assoc, ENNReal.mul_inv_cancel h1 h2, one_mul]

protected theorem mul_inv_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x * y⁻¹ ≤ z ↔ x ≤ z * y := by
  rw [mul_comm, ENNReal.inv_mul_le_iff h1 h2, mul_comm]

protected theorem div_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ z * y := by
  rw [div_eq_mul_inv, ENNReal.mul_inv_le_iff h1 h2]

protected theorem div_le_iff' {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ y * z := by
  rw [mul_comm, ENNReal.div_le_iff h1 h2]

protected theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction' b with b
  · replace ha : a ≠ 0 := ha.neg_resolve_right rfl
    simp [ha]
  induction' a with a
  · replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl)
    simp [hb]
  by_cases h'a : a = 0
  · simp only [h'a, top_mul, ENNReal.inv_zero, ENNReal.coe_ne_top, zero_mul, Ne,
      not_false_iff, ENNReal.coe_zero, ENNReal.inv_eq_zero]
  by_cases h'b : b = 0
  · simp only [h'b, ENNReal.inv_zero, ENNReal.coe_ne_top, mul_top, Ne, not_false_iff,
      mul_zero, ENNReal.coe_zero, ENNReal.inv_eq_zero]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_inv, ← ENNReal.coe_inv h'a, ← ENNReal.coe_inv h'b, ←
    ENNReal.coe_mul, mul_inv_rev, mul_comm]
  simp [h'a, h'b]

protected theorem inv_div {a b : ℝ≥0∞} (htop : b ≠ ∞ ∨ a ≠ ∞) (hzero : b ≠ 0 ∨ a ≠ 0) :
    (a / b)⁻¹ = b / a := by
  rw [← ENNReal.inv_ne_zero] at htop
  rw [← ENNReal.inv_ne_top] at hzero
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv htop hzero, mul_comm, inv_inv]

protected theorem mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hc'), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', one_mul]

protected theorem mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hc') (Or.inr hc), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', mul_one]

protected theorem sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero

theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  induction b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_gt

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_ge

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual

@[simp]
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]

@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne

@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]

/-- See `ENNReal.div_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma div_div_cancel' (h₀ : a = 0 → b = 0) (h₁ : a = ∞ → b = 0) :
    a / (a / b) = b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr ha') (Or.inr ha),
    ENNReal.div_mul_cancel ha ha']

/-- See `ENNReal.div_div_cancel'` for a stronger version. -/
protected lemma div_div_cancel {a b : ℝ≥0∞} (h₀ : a ≠ 0) (h₁ : a ≠ ∞) :
    a / (a / b) = b :=
  ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])

protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
    a ≤ c / b ↔ a * b ≤ c := by
  induction' b with b
  · lift c to ℝ≥0 using ht.neg_resolve_left rfl
    rw [div_top, nonpos_iff_eq_zero]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c ≠ 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_right hb coe_ne_top, ENNReal.div_mul_cancel hb coe_ne_top]

protected theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa

protected theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h

@[simp] protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]

@[simp] protected lemma mul_inv_le_one (a : ℝ≥0∞) : a * a⁻¹ ≤ 1 := ENNReal.div_self_le_one
@[simp] protected lemma inv_mul_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma mul_inv_ne_top (a : ℝ≥0∞) : a * a⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma inv_mul_ne_top (a : ℝ≥0∞) : a⁻¹ * a ≠ ⊤ := by simp [mul_comm]

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h

protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNReal.le_div_iff_mul_le h0 ht

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h

theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]

theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNReal.div_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)

protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h

protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr

lemma eq_of_forall_nnreal_iff {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x ↔ ↑r ≤ y) : x = y :=
  le_antisymm (le_of_forall_nnreal_lt fun _r hr ↦ (h _).1 hr.le)
    (le_of_forall_nnreal_lt fun _r hr ↦ (h _).2 hr.le)

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r

protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹

protected theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm

protected theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  ENNReal.mul_inv_cancel h0 hI

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl

theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNReal.mul_div_cancel ha ha'], fun h => by
    rw [← h, mul_div_assoc, ENNReal.mul_div_cancel ha ha']⟩

protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]

theorem div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_self two_ne_zero ofNat_ne_top]

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]

@[simp] theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]

protected lemma div_ne_zero : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ ∞ := by
  rw [← pos_iff_ne_zero, div_pos_iff]

protected lemma div_mul (a : ℝ≥0∞) (h0 : b ≠ 0 ∨ c ≠ 0) (htop : b ≠ ∞ ∨ c ≠ ∞) :
    a / b * c = a / (b / c) := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv, inv_inv]
  · ring
  · simpa
  · simpa

protected lemma mul_div_mul_comm (hc : c ≠ 0 ∨ d ≠ ∞) (hd : c ≠ ∞ ∨ d ≠ 0) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring

protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 :=
  ENNReal.div_pos h ofNat_ne_top

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two

protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]

protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  rw [← one_div, sub_half one_ne_top]

private lemma exists_lt_mul_left {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩

private lemma exists_lt_mul_right {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ b' < b, c < a * b' := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc

lemma mul_le_of_forall_lt {a b c : ℝ≥0∞} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact le_trans hd.le <| h _ ha' _ hb'

lemma le_mul_of_forall_lt {a b c : ℝ≥0∞} (h₁ : a ≠ 0 ∨ b ≠ ∞) (h₂ : a ≠ ∞ ∨ b ≠ 0)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  rw [← ENNReal.inv_le_inv, ENNReal.mul_inv h₁ h₂]
  exact mul_le_of_forall_lt fun a' ha' b' hb' ↦ ENNReal.le_inv_iff_le_inv.1 <|
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun _ => Subtype.ext <| toNNReal_coe _
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl

theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 ((zero_le _).trans_lt hn), by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
    ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn

theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*, npos.ne']

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_coe, coe_pow, zpow_natCast]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]

lemma zero_zpow_def (n : ℤ) : (0 : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤ := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

lemma top_zpow_def (n : ℤ) : (⊤ : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0 := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma zpow_ne_top {a : ℝ≥0∞} (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n ≠ ∞ :=
  (ENNReal.zpow_lt_top ha h'a n).ne

theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]

theorem exists_mem_Ioc_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]

theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using h

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h

protected theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]

protected theorem zpow_neg (x : ℝ≥0∞) (m : ℤ) : x ^ (-m) = (x ^ m)⁻¹ := by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])

protected theorem zpow_sub {x : ℝ≥0∞} (x_ne_zero : x ≠ 0) (x_ne_top : x ≠ ⊤) (m n : ℤ) :
    x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ := by
  rw [sub_eq_add_neg, ENNReal.zpow_add x_ne_zero x_ne_top, ENNReal.zpow_neg]

protected lemma inv_zpow (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  cases n <;> simp [ENNReal.inv_pow]

protected lemma inv_zpow' (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = x ^ (-n) := by
  rw [ENNReal.zpow_neg, ENNReal.inv_zpow]

lemma zpow_le_one_of_nonpos {n : ℤ} (hn : n ≤ 0) {x : ℝ≥0∞} (hx : 1 ≤ x) : x ^ n ≤ 1 := by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to ℕ using by simpa using hn
  rw [← ENNReal.inv_zpow', ENNReal.inv_zpow, ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx

lemma isUnit_iff : IsUnit a ↔ a ≠ 0 ∧ a ≠ ∞ := by
  refine ⟨fun ha ↦ ⟨ha.ne_zero, ?_⟩,
    fun ha ↦ ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  norm_cast at this
  simp [mul_inv_cancel] at this

/-- Left multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulLeftOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_left, ha.ne_zero, (isUnit_iff.1 ha).2]

/-- Right multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulRightOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_right, ha.ne_zero, (isUnit_iff.1 ha).2]

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

lemma mul_iSup (a : ℝ≥0∞) (f : ι → ℝ≥0∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

lemma iSup_mul (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp [mul_comm, mul_iSup]

lemma mul_sSup {a : ℝ≥0∞} : a * sSup s = ⨆ b ∈ s, a * b := by
  simp only [sSup_eq_iSup, mul_iSup]

lemma sSup_mul {a : ℝ≥0∞} : sSup s * a = ⨆ b ∈ s, b * a := by
  simp only [sSup_eq_iSup, iSup_mul]

lemma iSup_div (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : iSup f / a = ⨆ i, f i / a := iSup_mul ..
lemma sSup_div (s : Set ℝ≥0∞) (a : ℝ≥0∞) : sSup s / a = ⨆ b ∈ s, b / a := sSup_mul ..

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.mul_iInf_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.mul_iInf` for the special case assuming `Nonempty ι`. -/
lemma mul_iInf' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (∃ i, f i = 0)
    · rw [(iInf_eq_bot _).2, (iInf_eq_bot _).2, bot_eq_zero, mul_zero] <;>
        exact fun _ _↦ ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i ↦ top_mul fun hi ↦ hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.iInf_mul_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.iInf_mul` for the special case assuming `Nonempty ι`. -/
lemma iInf_mul' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    (⨅ i, f i) * a = ⨅ i, f i * a := by simpa only [mul_comm a] using mul_iInf' hinfty h₀

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`. -/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' (by simp [ha]) (by simp [ha₀])

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`. -/
lemma iInf_mul_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' (by simp [ha]) (by simp [ha₀])

/-- See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
lemma mul_iInf [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := mul_iInf' hinfty fun _ ↦ ‹Nonempty ι›

/-- See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
lemma iInf_mul [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := iInf_mul' hinfty fun _ ↦ ‹Nonempty ι›

/-- Very general version for distributivity of division over an infimum.

See `ENNReal.iInf_div_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.iInf_div` for the special case assuming `Nonempty ι`. -/
lemma iInf_div' (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = ∞ → Nonempty ι) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_mul' (by simpa) (by simpa)

/-- If `a ≠ 0` and `a ≠ ∞`, then division by `a` maps infimum to infimum.

See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div` for another special case that
assumes `Nonempty ι` but does not require `a ≠ ∞`. -/
lemma iInf_div_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : (⨅ i, f i) / a = ⨅ i, f i / a :=
  iInf_div' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div_of_ne` for another special
case that assumes `a ≠ ∞` but does not require `Nonempty ι`. -/
lemma iInf_div [Nonempty ι] (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_div' hinfty fun _ ↦ ‹Nonempty ι›

lemma inv_iInf (f : ι → ℝ≥0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := OrderIso.invENNReal.map_iInf _
lemma inv_iSup (f : ι → ℝ≥0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := OrderIso.invENNReal.map_iSup _

lemma inv_sInf (s : Set ℝ≥0∞) : (sInf s)⁻¹ = ⨆ a ∈ s, a⁻¹ := by simp [sInf_eq_iInf, inv_iInf]
lemma inv_sSup (s : Set ℝ≥0∞) : (sSup s)⁻¹ = ⨅ a ∈ s, a⁻¹ := by simp [sSup_eq_iSup, inv_iSup]

lemma le_iInf_mul {ι : Type*} (u v : ι → ℝ≥0∞) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  le_iInf fun i ↦ mul_le_mul' (iInf_le u i) (iInf_le v i)

lemma iSup_mul_le {ι : Type*} {u v : ι → ℝ≥0∞} :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun i ↦ mul_le_mul' (le_iSup u i) (le_iSup v i)


lemma le_iInf_mul_iInf {g : κ → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (ha : ∀ i j, a ≤ f i * g j) : a ≤ (⨅ i, f i) * ⨅ j, g j := by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j ≠ ∞ := by simpa using hg
  rw [iInf_mul fun h ↦ (hg h).elim, le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h ↦ (hi h).elim] using ha i

lemma iInf_mul_iInf {f g : ι → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (h : ∀ i j, ∃ k, f k * g k ≤ f i * g j) : (⨅ i, f i) * ⨅ i, g i = ⨅ i, f i * g i := by
  refine le_antisymm (le_iInf fun i ↦ mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j ↦ ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

lemma smul_iSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (f : ι → ℝ≥0∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

lemma smul_sSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (s : Set ℝ≥0∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]
theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]

theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy.le), ofReal_inv_of_pos hy]

@[simp] theorem toNNReal_inv (a : ℝ≥0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  induction' a with a; · simp
  rcases eq_or_ne a 0 with (rfl | ha); · simp
  rw [← coe_inv ha, toNNReal_coe, toNNReal_coe]

@[simp] theorem toNNReal_div (a b : ℝ≥0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv, toNNReal_mul, toNNReal_inv, div_eq_mul_inv]

@[simp] theorem toReal_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]

@[simp] theorem toReal_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, toReal_mul, toReal_inv, div_eq_mul_inv]

end Inv
end ENNReal
