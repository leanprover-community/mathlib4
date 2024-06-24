/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Operations

#align_import data.real.ennreal from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

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

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]
#align ennreal.div_eq_inv_mul ENNReal.div_eq_inv_mul

@[simp] theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show sInf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp
#align ennreal.inv_zero ENNReal.inv_zero

@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_le_of_dense fun a (h : 0 < a) => sInf_le <| by simp [*, h.ne', top_mul]
#align ennreal.inv_top ENNReal.inv_top

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb
#align ennreal.coe_inv_le ENNReal.coe_inv_le

@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <| sInf_le <| mem_setOf.2 <| by rw [← coe_mul, mul_inv_cancel hr, coe_one]
#align ennreal.coe_inv ENNReal.coe_inv

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]
#align ennreal.coe_inv_two ENNReal.coe_inv_two

@[simp, norm_cast]
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]
#align ennreal.coe_div ENNReal.coe_div

lemma coe_div_le : ↑(p / r) ≤ (p / r : ℝ≥0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using mul_le_mul_left' coe_inv_le _

theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]
#align ennreal.div_zero ENNReal.div_zero

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
#align ennreal.inv_pow ENNReal.inv_pow

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel h0
#align ennreal.mul_inv_cancel ENNReal.mul_inv_cancel

protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht
#align ennreal.inv_mul_cancel ENNReal.inv_mul_cancel

protected theorem div_mul_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : b / a * a = b := by
  rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel h0 hI, mul_one]
#align ennreal.div_mul_cancel ENNReal.div_mul_cancel

protected theorem mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b := by
  rw [mul_comm, ENNReal.div_mul_cancel h0 hI]
#align ennreal.mul_div_cancel' ENNReal.mul_div_cancel'

-- Porting note: `simp only [div_eq_mul_inv, mul_comm, mul_assoc]` doesn't work in the following two
protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_right_comm, ← mul_assoc]
#align ennreal.mul_comm_div ENNReal.mul_comm_div

protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]
#align ennreal.mul_div_right_comm ENNReal.mul_div_right_comm

instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [none_eq_top, some_eq_coe, -coe_inv, (coe_inv _).symm]

@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj
#align ennreal.inv_eq_top ENNReal.inv_eq_top

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp
#align ennreal.inv_ne_top ENNReal.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]
#align ennreal.inv_lt_top ENNReal.inv_lt_top

theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1 (inv_ne_top.mpr h2)
#align ennreal.div_lt_top ENNReal.div_lt_top

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj
#align ennreal.inv_eq_zero ENNReal.inv_eq_zero

protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp
#align ennreal.inv_ne_zero ENNReal.inv_ne_zero

protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
  ENNReal.mul_pos ha <| ENNReal.inv_ne_zero.2 hb
#align ennreal.div_pos ENNReal.div_pos

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
#align ennreal.mul_inv ENNReal.mul_inv

protected theorem mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hc'), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', one_mul]
#align ennreal.mul_div_mul_left ENNReal.mul_div_mul_left

protected theorem mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hc') (Or.inr hc), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', mul_one]
#align ennreal.mul_div_mul_right ENNReal.mul_div_mul_right

protected theorem sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)
#align ennreal.sub_div ENNReal.sub_div

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero
#align ennreal.inv_pos ENNReal.inv_pos

theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  induction b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact NNReal.inv_lt_inv ha h
#align ennreal.inv_strict_anti ENNReal.inv_strictAnti

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_lt
#align ennreal.inv_lt_inv ENNReal.inv_lt_inv

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹
#align ennreal.inv_lt_iff_inv_lt ENNReal.inv_lt_iff_inv_lt

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b
#align ennreal.lt_inv_iff_lt_inv ENNReal.lt_inv_iff_lt_inv

@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_le
#align ennreal.inv_le_inv ENNReal.inv_le_inv

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹
#align ennreal.inv_le_iff_inv_le ENNReal.inv_le_iff_inv_le

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b
#align ennreal.le_inv_iff_le_inv ENNReal.le_inv_iff_le_inv

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]
#align ennreal.inv_le_one ENNReal.inv_le_one

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]
#align ennreal.one_le_inv ENNReal.one_le_inv

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]
#align ennreal.inv_lt_one ENNReal.inv_lt_one

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]
#align ennreal.one_lt_inv ENNReal.one_lt_inv

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual
#align order_iso.inv_ennreal OrderIso.invENNReal
#align order_iso.inv_ennreal_apply OrderIso.invENNReal_apply

@[simp]
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl
#align order_iso.inv_ennreal_symm_apply OrderIso.invENNReal_symm_apply

@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]
#align ennreal.div_top ENNReal.div_top

-- Porting note: reordered 4 lemmas

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']
#align ennreal.top_div ENNReal.top_div

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]
#align ennreal.top_div_of_ne_top ENNReal.top_div_of_ne_top

@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top
#align ennreal.top_div_coe ENNReal.top_div_coe

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne
#align ennreal.top_div_of_lt_top ENNReal.top_div_of_lt_top

@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹
#align ennreal.zero_div ENNReal.zero_div

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]
#align ennreal.div_eq_top ENNReal.div_eq_top

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
#align ennreal.le_div_iff_mul_le ENNReal.le_div_iff_mul_le

protected theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa
#align ennreal.div_le_iff_le_mul ENNReal.div_le_iff_le_mul

protected theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)
#align ennreal.lt_div_iff_mul_lt ENNReal.lt_div_iff_mul_lt

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h
#align ennreal.div_le_of_le_mul ENNReal.div_le_of_le_mul

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align ennreal.div_le_of_le_mul' ENNReal.div_le_of_le_mul'

protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h
#align ennreal.mul_le_of_le_div ENNReal.mul_le_of_le_div

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h
#align ennreal.mul_le_of_le_div' ENNReal.mul_le_of_le_div'

protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNReal.le_div_iff_mul_le h0 ht
#align ennreal.div_lt_iff ENNReal.div_lt_iff

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h
#align ennreal.mul_lt_of_lt_div ENNReal.mul_lt_of_lt_div

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h
#align ennreal.mul_lt_of_lt_div' ENNReal.mul_lt_of_lt_div'

theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]

theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNReal.div_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]
#align ennreal.inv_le_iff_le_mul ENNReal.inv_le_iff_le_mul

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp
#align ennreal.le_inv_iff_mul_le ENNReal.le_inv_iff_mul_le

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)
#align ennreal.div_le_div ENNReal.div_le_div

@[gcongr] protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h
#align ennreal.div_le_div_left ENNReal.div_le_div_left

@[gcongr] protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl
#align ennreal.div_le_div_right ENNReal.div_le_div_right

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h
#align ennreal.eq_inv_of_mul_eq_one_left ENNReal.eq_inv_of_mul_eq_one_left

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]
#align ennreal.mul_le_iff_le_inv ENNReal.mul_le_iff_le_inv

instance : PosSMulStrictMono ℝ≥0 ℝ≥0∞ where
  elim _r hr _a _b hab := ENNReal.mul_lt_mul_left' (coe_pos.2 hr).ne' coe_ne_top hab

instance : SMulPosMono ℝ≥0 ℝ≥0∞ where
  elim _r _ _a _b hab := mul_le_mul_right' (coe_le_coe.2 hab) _

#align ennreal.le_inv_smul_iff_of_pos le_inv_smul_iff_of_pos
#align ennreal.inv_smul_le_iff_of_pos inv_smul_le_iff_of_pos

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine le_of_forall_ge_of_dense fun r hr => ?_
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr
#align ennreal.le_of_forall_nnreal_lt ENNReal.le_of_forall_nnreal_lt

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr
#align ennreal.le_of_forall_pos_nnreal_lt ENNReal.le_of_forall_pos_nnreal_lt

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r
#align ennreal.eq_top_of_forall_nnreal_le ENNReal.eq_top_of_forall_nnreal_le

protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹
#align ennreal.add_div ENNReal.add_div

protected theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm
#align ennreal.div_add_div_same ENNReal.div_add_div_same

protected theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  ENNReal.mul_inv_cancel h0 hI
#align ennreal.div_self ENNReal.div_self

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl
#align ennreal.mul_div_le ENNReal.mul_div_le

theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNReal.mul_div_cancel' ha ha'], fun h => by
    rw [← h, mul_div_assoc, ENNReal.mul_div_cancel' ha ha']⟩
#align ennreal.eq_div_iff ENNReal.eq_div_iff

protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]
#align ennreal.div_eq_div_iff ENNReal.div_eq_div_iff

theorem div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩
#align ennreal.div_eq_one_iff ENNReal.div_eq_one_iff

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_self two_ne_zero two_ne_top]
#align ennreal.inv_two_add_inv_two ENNReal.inv_two_add_inv_two

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 :=
  calc (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ := by ring
  _ = 1 := ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 <| by decide) coe_ne_top
#align ennreal.inv_three_add_inv_three ENNReal.inv_three_add_inv_three

@[simp]
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]
#align ennreal.add_halves ENNReal.add_halves

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]
#align ennreal.add_thirds ENNReal.add_thirds

@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]
#align ennreal.div_zero_iff ENNReal.div_eq_zero_iff

@[simp] theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]
#align ennreal.div_pos_iff ENNReal.div_pos_iff

protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 := by
  simp only [div_pos_iff, ne_eq, h, not_false_eq_true, two_ne_top, and_self]
#align ennreal.half_pos ENNReal.half_pos

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two
#align ennreal.one_half_lt_one ENNReal.one_half_lt_one

protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]
#align ennreal.half_lt_self ENNReal.half_lt_self

protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _
#align ennreal.half_le_self ENNReal.half_le_self

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := by
  lift a to ℝ≥0 using h
  exact sub_eq_of_add_eq (mul_ne_top coe_ne_top <| by simp) (ENNReal.add_halves a)
#align ennreal.sub_half ENNReal.sub_half

@[simp]
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  simpa only [div_eq_mul_inv, one_mul] using sub_half one_ne_top
#align ennreal.one_sub_inv_two ENNReal.one_sub_inv_two

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, Subtype.coe_mk, tsub_add_cancel_of_le this]
#align ennreal.order_iso_Iic_one_birational ENNReal.orderIsoIicOneBirational

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl
#align ennreal.order_iso_Iic_one_birational_symm_apply ENNReal.orderIsoIicOneBirational_symm_apply

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun x => Subtype.ext <| toNNReal_coe
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }
#align ennreal.order_iso_Iic_coe ENNReal.orderIsoIicCoe

@[simp]
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl
#align ennreal.order_iso_Iic_coe_symm_apply_coe ENNReal.orderIsoIicCoe_symm_apply_coe

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm
#align ennreal.order_iso_unit_interval_birational ENNReal.orderIsoUnitIntervalBirational

@[simp]
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl
#align ennreal.order_iso_unit_interval_birational_apply_coe ENNReal.orderIsoUnitIntervalBirational_apply_coe

theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]
#align ennreal.exists_inv_nat_lt ENNReal.exists_inv_nat_lt

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 ((zero_le _).trans_lt hn), by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩
#align ennreal.exists_nat_pos_mul_gt ENNReal.exists_nat_pos_mul_gt

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right
#align ennreal.exists_nat_mul_gt ENNReal.exists_nat_mul_gt

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
    ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn
#align ennreal.exists_nat_pos_inv_mul_lt ENNReal.exists_nat_pos_inv_mul_lt

theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*, npos.ne', zero_lt_one]
#align ennreal.exists_nnreal_pos_mul_lt ENNReal.exists_nnreal_pos_mul_lt

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow
#align ennreal.exists_inv_two_pow_lt ENNReal.exists_inv_two_pow_lt

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n := by
  cases' n with n n
  · simp only [Int.ofNat_eq_coe, coe_pow, zpow_natCast]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]
#align ennreal.coe_zpow ENNReal.coe_zpow

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, not_false, ENNReal.inv_pos, false_and,
      not_false_eq_true]
#align ennreal.zpow_pos ENNReal.zpow_pos

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top _
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]
#align ennreal.zpow_lt_top ENNReal.zpow_lt_top

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
#align ennreal.exists_mem_Ico_zpow ENNReal.exists_mem_Ico_zpow

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
#align ennreal.exists_mem_Ioc_zpow ENNReal.exists_mem_Ioc_zpow

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
#align ennreal.Ioo_zero_top_eq_Union_Ico_zpow ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow

@[gcongr]
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  induction' a with a a <;> induction' b with b b
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_le_pow_right hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.ofNat_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_le_pow_right hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.ofNat_add, Int.ofNat_one, Int.negSucc_eq] using
      h
#align ennreal.zpow_le_of_le ENNReal.zpow_le_of_le

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h
#align ennreal.monotone_zpow ENNReal.monotone_zpow

protected theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
#align ennreal.zpow_add ENNReal.zpow_add

end Inv
end ENNReal
