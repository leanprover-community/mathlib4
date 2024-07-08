/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Tactic.Positivity.Core

#align_import algebra.order.field.basic from "leanprover-community/mathlib"@"84771a9f5f0bd5e5d6218811556508ddf476dcbd"

/-!
# Lemmas about linear ordered (semi)fields
-/


open Function OrderDual

variable {ι α β : Type*}

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {a b c d e : α} {m n : ℤ}

/-- `Equiv.mulLeft₀` as an order_iso. -/
@[simps! (config := { simpRhs := true })]
def OrderIso.mulLeft₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equiv.mulLeft₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_left ha }
#align order_iso.mul_left₀ OrderIso.mulLeft₀
#align order_iso.mul_left₀_symm_apply OrderIso.mulLeft₀_symm_apply
#align order_iso.mul_left₀_apply OrderIso.mulLeft₀_apply

/-- `Equiv.mulRight₀` as an order_iso. -/
@[simps! (config := { simpRhs := true })]
def OrderIso.mulRight₀ (a : α) (ha : 0 < a) : α ≃o α :=
  { Equiv.mulRight₀ a ha.ne' with map_rel_iff' := @fun _ _ => mul_le_mul_right ha }
#align order_iso.mul_right₀ OrderIso.mulRight₀
#align order_iso.mul_right₀_symm_apply OrderIso.mulRight₀_symm_apply
#align order_iso.mul_right₀_apply OrderIso.mulRight₀_apply

/-!
### Relating one division with another term.
-/


theorem le_div_iff (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨fun h => div_mul_cancel₀ b (ne_of_lt hc).symm ▸ mul_le_mul_of_nonneg_right h hc.le, fun h =>
    calc
      a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc).symm
      _ ≤ b * (1 / c) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hc).le
      _ = b / c := (div_eq_mul_one_div b c).symm
      ⟩
#align le_div_iff le_div_iff

theorem le_div_iff' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by rw [mul_comm, le_div_iff hc]
#align le_div_iff' le_div_iff'

theorem div_le_iff (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
  ⟨fun h =>
    calc
      a = a / b * b := by rw [div_mul_cancel₀ _ (ne_of_lt hb).symm]
      _ ≤ c * b := mul_le_mul_of_nonneg_right h hb.le
      ,
    fun h =>
    calc
      a / b = a * (1 / b) := div_eq_mul_one_div a b
      _ ≤ c * b * (1 / b) := mul_le_mul_of_nonneg_right h (one_div_pos.2 hb).le
      _ = c * b / b := (div_eq_mul_one_div (c * b) b).symm
      _ = c := by refine (div_eq_iff (ne_of_gt hb)).mpr rfl
      ⟩
#align div_le_iff div_le_iff

theorem div_le_iff' (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c := by rw [mul_comm, div_le_iff hb]
#align div_le_iff' div_le_iff'

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  rw [div_le_iff hb, div_le_iff' hc]

theorem lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le <| div_le_iff hc
#align lt_div_iff lt_div_iff

theorem lt_div_iff' (hc : 0 < c) : a < b / c ↔ c * a < b := by rw [mul_comm, lt_div_iff hc]
#align lt_div_iff' lt_div_iff'

theorem div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (le_div_iff hc)
#align div_lt_iff div_lt_iff

theorem div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a := by rw [mul_comm, div_lt_iff hc]
#align div_lt_iff' div_lt_iff'

lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff hb, div_lt_iff' hc]

theorem inv_mul_le_iff (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_le_iff' h
#align inv_mul_le_iff inv_mul_le_iff

theorem inv_mul_le_iff' (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ c * b := by rw [inv_mul_le_iff h, mul_comm]
#align inv_mul_le_iff' inv_mul_le_iff'

theorem mul_inv_le_iff (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ b * c := by rw [mul_comm, inv_mul_le_iff h]
#align mul_inv_le_iff mul_inv_le_iff

theorem mul_inv_le_iff' (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ c * b := by rw [mul_comm, inv_mul_le_iff' h]
#align mul_inv_le_iff' mul_inv_le_iff'

theorem div_self_le_one (a : α) : a / a ≤ 1 :=
  if h : a = 0 then by simp [h] else by simp [h]
#align div_self_le_one div_self_le_one

theorem inv_mul_lt_iff (h : 0 < b) : b⁻¹ * a < c ↔ a < b * c := by
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div]
  exact div_lt_iff' h
#align inv_mul_lt_iff inv_mul_lt_iff

theorem inv_mul_lt_iff' (h : 0 < b) : b⁻¹ * a < c ↔ a < c * b := by rw [inv_mul_lt_iff h, mul_comm]
#align inv_mul_lt_iff' inv_mul_lt_iff'

theorem mul_inv_lt_iff (h : 0 < b) : a * b⁻¹ < c ↔ a < b * c := by rw [mul_comm, inv_mul_lt_iff h]
#align mul_inv_lt_iff mul_inv_lt_iff

theorem mul_inv_lt_iff' (h : 0 < b) : a * b⁻¹ < c ↔ a < c * b := by rw [mul_comm, inv_mul_lt_iff' h]
#align mul_inv_lt_iff' mul_inv_lt_iff'

theorem inv_pos_le_iff_one_le_mul (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [inv_eq_one_div]
  exact div_le_iff ha
#align inv_pos_le_iff_one_le_mul inv_pos_le_iff_one_le_mul

theorem inv_pos_le_iff_one_le_mul' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [inv_eq_one_div]
  exact div_le_iff' ha
#align inv_pos_le_iff_one_le_mul' inv_pos_le_iff_one_le_mul'

theorem inv_pos_lt_iff_one_lt_mul (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [inv_eq_one_div]
  exact div_lt_iff ha
#align inv_pos_lt_iff_one_lt_mul inv_pos_lt_iff_one_lt_mul

theorem inv_pos_lt_iff_one_lt_mul' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [inv_eq_one_div]
  exact div_lt_iff' ha
#align inv_pos_lt_iff_one_lt_mul' inv_pos_lt_iff_one_lt_mul'

/-- One direction of `div_le_iff` where `b` is allowed to be `0` (but `c` must be nonnegative) -/
theorem div_le_of_nonneg_of_le_mul (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c := by
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · simp only [div_zero, hc]
  · rwa [div_le_iff hb']
#align div_le_of_nonneg_of_le_mul div_le_of_nonneg_of_le_mul

/-- One direction of `div_le_iff` where `c` is allowed to be `0` (but `b` must be nonnegative) -/
lemma mul_le_of_nonneg_of_le_div (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_div_iff hc] at h
#align mul_le_of_nonneg_of_le_div mul_le_of_nonneg_of_le_div

theorem div_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_nonneg_of_le_mul hb zero_le_one <| by rwa [one_mul]
#align div_le_one_of_le div_le_one_of_le

lemma mul_inv_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 := by
  simpa only [← div_eq_mul_inv] using div_le_one_of_le h hb

lemma inv_mul_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 := by
  simpa only [← div_eq_inv_mul] using div_le_one_of_le h hb

/-!
### Bi-implications of inequalities using inversions
-/

@[gcongr]
theorem inv_le_inv_of_le (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  rwa [← one_div a, le_div_iff' ha, ← div_eq_mul_inv, div_le_iff (ha.trans_le h), one_mul]
#align inv_le_inv_of_le inv_le_inv_of_le

/-- See `inv_le_inv_of_le` for the implication from right-to-left with one fewer assumption. -/
theorem inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff ha, ← div_eq_inv_mul, le_div_iff hb, one_mul]
#align inv_le_inv inv_le_inv

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ ≤ b ↔ b⁻¹ ≤ a`.
See also `inv_le_of_inv_le` for a one-sided implication with one fewer assumption. -/
theorem inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv]
#align inv_le inv_le

theorem inv_le_of_inv_le (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le ha ((inv_pos.2 ha).trans_le h)).1 h
#align inv_le_of_inv_le inv_le_of_inv_le

theorem le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv]
#align le_inv le_inv

/-- See `inv_lt_inv_of_lt` for the implication from right-to-left with one fewer assumption. -/
theorem inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)
#align inv_lt_inv inv_lt_inv

@[gcongr]
theorem inv_lt_inv_of_lt (hb : 0 < b) (h : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv (hb.trans h) hb).2 h
#align inv_lt_inv_of_lt inv_lt_inv_of_lt

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ < b ↔ b⁻¹ < a`.
See also `inv_lt_of_inv_lt` for a one-sided implication with one fewer assumption. -/
theorem inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv hb ha)
#align inv_lt inv_lt

theorem inv_lt_of_inv_lt (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt ha ((inv_pos.2 ha).trans h)).1 h
#align inv_lt_of_inv_lt inv_lt_of_inv_lt

theorem lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
  lt_iff_lt_of_le_iff_le (inv_le hb ha)
#align lt_inv lt_inv

theorem inv_lt_one (ha : 1 < a) : a⁻¹ < 1 := by
  rwa [inv_lt (zero_lt_one.trans ha) zero_lt_one, inv_one]
#align inv_lt_one inv_lt_one

theorem one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ := by
  rwa [lt_inv (@zero_lt_one α _ _ _ _ _) h₁, inv_one]
#align one_lt_inv one_lt_inv

theorem inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by
  rwa [inv_le (zero_lt_one.trans_le ha) zero_lt_one, inv_one]
#align inv_le_one inv_le_one

theorem one_le_inv (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ a⁻¹ := by
  rwa [le_inv (@zero_lt_one α _ _ _ _ _) h₁, inv_one]
#align one_le_inv one_le_inv

theorem inv_lt_one_iff_of_pos (h₀ : 0 < a) : a⁻¹ < 1 ↔ 1 < a :=
  ⟨fun h₁ => inv_inv a ▸ one_lt_inv (inv_pos.2 h₀) h₁, inv_lt_one⟩
#align inv_lt_one_iff_of_pos inv_lt_one_iff_of_pos

theorem inv_lt_one_iff : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  rcases le_or_lt a 0 with ha | ha
  · simp [ha, (inv_nonpos.2 ha).trans_lt zero_lt_one]
  · simp only [ha.not_le, false_or_iff, inv_lt_one_iff_of_pos ha]
#align inv_lt_one_iff inv_lt_one_iff

theorem one_lt_inv_iff : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ inv_lt_one h⟩, and_imp.2 one_lt_inv⟩
#align one_lt_inv_iff one_lt_inv_iff

theorem inv_le_one_iff : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  rcases em (a = 1) with (rfl | ha)
  · simp [le_rfl]
  · simp only [Ne.le_iff_lt (Ne.symm ha), Ne.le_iff_lt (mt inv_eq_one.1 ha), inv_lt_one_iff]
#align inv_le_one_iff inv_le_one_iff

theorem one_le_inv_iff : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 :=
  ⟨fun h => ⟨inv_pos.1 (zero_lt_one.trans_le h), inv_inv a ▸ inv_le_one h⟩, and_imp.2 one_le_inv⟩
#align one_le_inv_iff one_le_inv_iff

/-!
### Relating two divisions.
-/


@[mono, gcongr]
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonneg_right hab (one_div_nonneg.2 hc)
#align div_le_div_of_le_of_nonneg div_le_div_of_nonneg_right

@[gcongr]
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
#align div_lt_div_of_lt div_lt_div_of_pos_right

-- Not a `mono` lemma b/c `div_le_div` is strictly more general
@[gcongr]
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv (hc.trans_le h) hc).mpr h) ha
#align div_le_div_of_le_left div_le_div_of_nonneg_left

@[gcongr]
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c := by
  simpa only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv (hc.trans h) hc]
#align div_lt_div_of_lt_left div_lt_div_of_pos_left

@[deprecated (since := "2024-02-16")] alias div_le_div_of_le_of_nonneg := div_le_div_of_nonneg_right
@[deprecated (since := "2024-02-16")] alias div_lt_div_of_lt := div_lt_div_of_pos_right
@[deprecated (since := "2024-02-16")] alias div_le_div_of_le_left := div_le_div_of_nonneg_left
@[deprecated (since := "2024-02-16")] alias div_lt_div_of_lt_left := div_lt_div_of_pos_left

@[deprecated div_le_div_of_nonneg_right (since := "2024-02-16")]
lemma div_le_div_of_le (hc : 0 ≤ c) (hab : a ≤ b) : a / c ≤ b / c :=
  div_le_div_of_nonneg_right hab hc
#align div_le_div_of_le div_le_div_of_le

theorem div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
  ⟨le_imp_le_of_lt_imp_lt fun hab ↦ div_lt_div_of_pos_right hab hc,
    fun hab ↦ div_le_div_of_nonneg_right hab hc.le⟩
#align div_le_div_right div_le_div_right

theorem div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| div_le_div_right hc
#align div_lt_div_right div_lt_div_right

theorem div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b := by
  simp only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv hb hc]
#align div_lt_div_left div_lt_div_left

theorem div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)
#align div_le_div_left div_le_div_left

theorem div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]
#align div_lt_div_iff div_lt_div_iff

theorem div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]
#align div_le_div_iff div_le_div_iff

@[mono, gcongr]
theorem div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d := by
  rw [div_le_div_iff (hd.trans_le hbd) hd]
  exact mul_le_mul hac hbd hd.le hc
#align div_le_div div_le_div

@[gcongr]
theorem div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) : a / b < c / d :=
  (div_lt_div_iff (d0.trans_le hbd) d0).2 (mul_lt_mul hac hbd d0 c0)
#align div_lt_div div_lt_div

theorem div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) : a / b < c / d :=
  (div_lt_div_iff (d0.trans hbd) d0).2 (mul_lt_mul' hac hbd d0.le c0)
#align div_lt_div' div_lt_div'

/-!
### Relating one division and involving `1`
-/


theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb
#align div_le_self div_le_self

theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [div_one] using div_lt_div_of_pos_left ha zero_lt_one hb
#align div_lt_self div_lt_self

theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁
#align le_div_self le_div_self

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff hb, one_mul]
#align one_le_div one_le_div

theorem div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff hb, one_mul]
#align div_le_one div_le_one

theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff hb, one_mul]
#align one_lt_div one_lt_div

theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff hb, one_mul]
#align div_lt_one div_lt_one

theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := by simpa using inv_le ha hb
#align one_div_le one_div_le

theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by simpa using inv_lt ha hb
#align one_div_lt one_div_lt

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by simpa using le_inv ha hb
#align le_one_div le_one_div

theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by simpa using lt_inv ha hb
#align lt_one_div lt_one_div

/-!
### Relating two divisions, involving `1`
-/


theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa using inv_le_inv_of_le ha h
#align one_div_le_one_div_of_le one_div_le_one_div_of_le

theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  rwa [lt_div_iff' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]
#align one_div_lt_one_div_of_lt one_div_lt_one_div_of_lt

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_lt ha) h
#align le_of_one_div_le_one_div le_of_one_div_le_one_div

theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h
#align lt_of_one_div_lt_one_div lt_of_one_div_lt_one_div

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  div_le_div_left zero_lt_one ha hb
#align one_div_le_one_div one_div_le_one_div

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_left zero_lt_one ha hb
#align one_div_lt_one_div one_div_lt_one_div

theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]
#align one_lt_one_div one_lt_one_div

theorem one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]
#align one_le_one_div one_le_one_div

/-!
### Results about halving.
The equalities also hold in semifields of characteristic `0`.
-/


/- TODO: Unify `add_halves` and `add_halves'` into a single lemma about
`DivisionSemiring` + `CharZero` -/
theorem add_halves (a : α) : a / 2 + a / 2 = a := by
  rw [div_add_div_same, ← two_mul, mul_div_cancel_left₀ a two_ne_zero]
#align add_halves add_halves

-- TODO: Generalize to `DivisionSemiring`
theorem add_self_div_two (a : α) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel_right₀ a two_ne_zero]
#align add_self_div_two add_self_div_two

theorem half_pos (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two
#align half_pos half_pos

theorem one_half_pos : (0 : α) < 1 / 2 :=
  half_pos zero_lt_one
#align one_half_pos one_half_pos

@[simp]
theorem half_le_self_iff : a / 2 ≤ a ↔ 0 ≤ a := by
  rw [div_le_iff (zero_lt_two' α), mul_two, le_add_iff_nonneg_left]
#align half_le_self_iff half_le_self_iff

@[simp]
theorem half_lt_self_iff : a / 2 < a ↔ 0 < a := by
  rw [div_lt_iff (zero_lt_two' α), mul_two, lt_add_iff_pos_left]
#align half_lt_self_iff half_lt_self_iff

alias ⟨_, half_le_self⟩ := half_le_self_iff
#align half_le_self half_le_self

alias ⟨_, half_lt_self⟩ := half_lt_self_iff
#align half_lt_self half_lt_self

alias div_two_lt_of_pos := half_lt_self
#align div_two_lt_of_pos div_two_lt_of_pos

theorem one_half_lt_one : (1 / 2 : α) < 1 :=
  half_lt_self zero_lt_one
#align one_half_lt_one one_half_lt_one

theorem two_inv_lt_one : (2⁻¹ : α) < 1 :=
  (one_div _).symm.trans_lt one_half_lt_one
#align two_inv_lt_one two_inv_lt_one

theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff, mul_two]
#align left_lt_add_div_two left_lt_add_div_two

theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff, mul_two]
#align add_div_two_lt_right add_div_two_lt_right

theorem add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_add_div_same, div_add_div_same, ← two_mul, ← add_one_mul 2 a, two_add_one_eq_three,
    mul_div_cancel_left₀ a three_ne_zero]

/-!
### Miscellaneous lemmas
-/

@[simp] lemma div_pos_iff_of_pos_left (ha : 0 < a) : 0 < a / b ↔ 0 < b := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]

@[simp] lemma div_pos_iff_of_pos_right (hb : 0 < b) : 0 < a / b ↔ 0 < a := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]

theorem mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c := by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff hc]
#align mul_le_mul_of_mul_div_le mul_le_mul_of_mul_div_le

theorem div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) :
    a / (b * e) ≤ c / (d * e) := by
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 he)
#align div_mul_le_div_mul_of_div_le_div div_mul_le_div_mul_of_div_le_div

theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff this, div_div_cancel' h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)
#align exists_pos_mul_lt exists_pos_mul_lt

theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b < c * a :=
  let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff hc₀]⟩
#align exists_pos_lt_mul exists_pos_lt_mul

lemma monotone_div_right_of_nonneg (ha : 0 ≤ a) : Monotone (· / a) :=
  fun _b _c hbc ↦ div_le_div_of_nonneg_right hbc ha

lemma strictMono_div_right_of_pos (ha : 0 < a) : StrictMono (· / a) :=
  fun _b _c hbc ↦ div_lt_div_of_pos_right hbc ha

theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
    (hc : 0 ≤ c) : Monotone fun x => f x / c := (monotone_div_right_of_nonneg hc).comp hf
#align monotone.div_const Monotone.div_const

theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f) {c : α}
    (hc : 0 < c) : StrictMono fun x => f x / c := by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)
#align strict_mono.div_const StrictMono.div_const

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered α where
  dense a₁ a₂ h :=
    ⟨(a₁ + a₂) / 2,
      calc
        a₁ = (a₁ + a₁) / 2 := (add_self_div_two a₁).symm
        _ < (a₁ + a₂) / 2 := div_lt_div_of_pos_right (add_lt_add_left h _) zero_lt_two
        ,
      calc
        (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := div_lt_div_of_pos_right (add_lt_add_right h _) zero_lt_two
        _ = a₂ := add_self_div_two a₂
        ⟩
#align linear_ordered_field.to_densely_ordered LinearOrderedSemiField.toDenselyOrdered

theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c :=
  (monotone_div_right_of_nonneg hc).map_min.symm
#align min_div_div_right min_div_div_right

theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c :=
  (monotone_div_right_of_nonneg hc).map_max.symm
#align max_div_div_right max_div_div_right

theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) :=
  fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy
#align one_div_strict_anti_on one_div_strictAntiOn

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
    1 / a ^ n ≤ 1 / a ^ m := by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_le_pow_right a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _
#align one_div_pow_le_one_div_pow_of_le one_div_pow_le_one_div_pow_of_le

theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
    1 / a ^ n < 1 / a ^ m := by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _
#align one_div_pow_lt_one_div_pow_of_lt one_div_pow_lt_one_div_pow_of_lt

theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1
#align one_div_pow_anti one_div_pow_anti

theorem one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt a1
#align one_div_pow_strict_anti one_div_pow_strictAnti

theorem inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0) := fun _ hx _ hy xy =>
  (inv_lt_inv hy hx).2 xy
#align inv_strict_anti_on inv_strictAntiOn

theorem inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ := by
  convert one_div_pow_le_one_div_pow_of_le a1 mn using 1 <;> simp
#align inv_pow_le_inv_pow_of_le inv_pow_le_inv_pow_of_le

theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn using 1 <;> simp
#align inv_pow_lt_inv_pow_of_lt inv_pow_lt_inv_pow_of_lt

theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_le_inv_pow_of_le a1
#align inv_pow_anti inv_pow_anti

theorem inv_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_lt_inv_pow_of_lt a1
#align inv_pow_strict_anti inv_pow_strictAnti

/-! ### Results about `IsGLB` -/


theorem IsGLB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton
#align is_glb.mul_left IsGLB.mul_left

theorem IsGLB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha
#align is_glb.mul_right IsGLB.mul_right

end LinearOrderedSemifield

section

variable [LinearOrderedField α] {a b c d : α} {n : ℤ}

/-! ### Lemmas about pos, nonneg, nonpos, neg -/


theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]
#align div_pos_iff div_pos_iff

theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  simp [division_def, mul_neg_iff]
#align div_neg_iff div_neg_iff

theorem div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp [division_def, mul_nonneg_iff]
#align div_nonneg_iff div_nonneg_iff

theorem div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  simp [division_def, mul_nonpos_iff]
#align div_nonpos_iff div_nonpos_iff

theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
  div_nonneg_iff.2 <| Or.inr ⟨ha, hb⟩
#align div_nonneg_of_nonpos div_nonneg_of_nonpos

theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  div_pos_iff.2 <| Or.inr ⟨ha, hb⟩
#align div_pos_of_neg_of_neg div_pos_of_neg_of_neg

theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  div_neg_iff.2 <| Or.inr ⟨ha, hb⟩
#align div_neg_of_neg_of_pos div_neg_of_neg_of_pos

theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  div_neg_iff.2 <| Or.inl ⟨ha, hb⟩
#align div_neg_of_pos_of_neg div_neg_of_pos_of_neg

/-! ### Relating one division with another term -/


theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
  ⟨fun h => div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le, fun h =>
    calc
      a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
      _ ≥ b * (1 / c) := mul_le_mul_of_nonpos_right h (one_div_neg.2 hc).le
      _ = b / c := (div_eq_mul_one_div b c).symm
      ⟩
#align div_le_iff_of_neg div_le_iff_of_neg

theorem div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b := by
  rw [mul_comm, div_le_iff_of_neg hc]
#align div_le_iff_of_neg' div_le_iff_of_neg'

theorem le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c := by
  rw [← neg_neg c, mul_neg, div_neg, le_neg, div_le_iff (neg_pos.2 hc), neg_mul]
#align le_div_iff_of_neg le_div_iff_of_neg

theorem le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a := by
  rw [mul_comm, le_div_iff_of_neg hc]
#align le_div_iff_of_neg' le_div_iff_of_neg'

theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
  lt_iff_lt_of_le_iff_le <| le_div_iff_of_neg hc
#align div_lt_iff_of_neg div_lt_iff_of_neg

theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm, div_lt_iff_of_neg hc]
#align div_lt_iff_of_neg' div_lt_iff_of_neg'

theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le <| div_le_iff_of_neg hc
#align lt_div_iff_of_neg lt_div_iff_of_neg

theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm, lt_div_iff_of_neg hc]
#align lt_div_iff_of_neg' lt_div_iff_of_neg'

theorem div_le_one_of_ge (h : b ≤ a) (hb : b ≤ 0) : a / b ≤ 1 := by
  simpa only [neg_div_neg_eq] using div_le_one_of_le (neg_le_neg h) (neg_nonneg_of_nonpos hb)
#align div_le_one_of_ge div_le_one_of_ge

/-! ### Bi-implications of inequalities using inversions -/


theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mul]
#align inv_le_inv_of_neg inv_le_inv_of_neg

theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero.2 ha), inv_inv]
#align inv_le_of_neg inv_le_of_neg

theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv_of_neg (inv_lt_zero.2 hb) ha, inv_inv]
#align le_inv_of_neg le_inv_of_neg

theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)
#align inv_lt_inv_of_neg inv_lt_inv_of_neg

theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
  lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)
#align inv_lt_of_neg inv_lt_of_neg

theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ :=
  lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)
#align lt_inv_of_neg lt_inv_of_neg

/-!
### Monotonicity results involving inversion
-/


theorem sub_inv_antitoneOn_Ioi :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Ioi c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv (sub_pos.mpr hb) (sub_pos.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

theorem sub_inv_antitoneOn_Iio :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Iio c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

theorem sub_inv_antitoneOn_Icc_right (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact sub_inv_antitoneOn_Ioi.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem sub_inv_antitoneOn_Icc_left (ha : b < c) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact sub_inv_antitoneOn_Iio.mono <| (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_Ioi :
    AntitoneOn (fun x:α ↦ x⁻¹) (Set.Ioi 0) := by
  convert sub_inv_antitoneOn_Ioi
  exact (sub_zero _).symm

theorem inv_antitoneOn_Iio :
    AntitoneOn (fun x:α ↦ x⁻¹) (Set.Iio 0) := by
  convert sub_inv_antitoneOn_Iio
  exact (sub_zero _).symm

theorem inv_antitoneOn_Icc_right (ha : 0 < a) :
    AntitoneOn (fun x:α ↦ x⁻¹) (Set.Icc a b) := by
  convert sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

theorem inv_antitoneOn_Icc_left (hb : b < 0) :
    AntitoneOn (fun x:α ↦ x⁻¹) (Set.Icc a b) := by
  convert sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm

/-! ### Relating two divisions -/


theorem div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonpos_right h (one_div_nonpos.2 hc)
#align div_le_div_of_nonpos_of_le div_le_div_of_nonpos_of_le

theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)
#align div_lt_div_of_neg_of_lt div_lt_div_of_neg_of_lt

theorem div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
  ⟨le_imp_le_of_lt_imp_lt <| div_lt_div_of_neg_of_lt hc, div_le_div_of_nonpos_of_le <| hc.le⟩
#align div_le_div_right_of_neg div_le_div_right_of_neg

theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
  lt_iff_lt_of_le_iff_le <| div_le_div_right_of_neg hc
#align div_lt_div_right_of_neg div_lt_div_right_of_neg

/-! ### Relating one division and involving `1` -/


theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by rw [le_div_iff_of_neg hb, one_mul]
#align one_le_div_of_neg one_le_div_of_neg

theorem div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a := by rw [div_le_iff_of_neg hb, one_mul]
#align div_le_one_of_neg div_le_one_of_neg

theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by rw [lt_div_iff_of_neg hb, one_mul]
#align one_lt_div_of_neg one_lt_div_of_neg

theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by rw [div_lt_iff_of_neg hb, one_mul]
#align div_lt_one_of_neg div_lt_one_of_neg

theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le_of_neg ha hb
#align one_div_le_of_neg one_div_le_of_neg

theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_of_neg ha hb
#align one_div_lt_of_neg one_div_lt_of_neg

theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_of_neg ha hb
#align le_one_div_of_neg le_one_div_of_neg

theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_of_neg ha hb
#align lt_one_div_of_neg lt_one_div_of_neg

theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_lt, one_lt_div_of_neg]
  · simp [lt_irrefl, zero_le_one]
  · simp [hb, hb.not_lt, one_lt_div]
#align one_lt_div_iff one_lt_div_iff

theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_lt, one_le_div_of_neg]
  · simp [lt_irrefl, zero_lt_one.not_le, zero_lt_one]
  · simp [hb, hb.not_lt, one_le_div]
#align one_le_div_iff one_le_div_iff

theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_lt, hb.ne, div_lt_one_of_neg]
  · simp [zero_lt_one]
  · simp [hb, hb.not_lt, div_lt_one, hb.ne.symm]
#align div_lt_one_iff div_lt_one_iff

theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_lt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_lt, div_le_one, hb.ne.symm]
#align div_le_one_iff div_le_one_iff

/-! ### Relating two divisions, involving `1` -/


theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]
#align one_div_le_one_div_of_neg_of_le one_div_le_one_div_of_neg_of_le

theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]
#align one_div_lt_one_div_of_neg_of_lt one_div_lt_one_div_of_neg_of_lt

theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
  le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_neg_of_lt hb) h
#align le_of_neg_of_one_div_le_one_div le_of_neg_of_one_div_le_one_div

theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
  lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h
#align lt_of_neg_of_one_div_lt_one_div lt_of_neg_of_one_div_lt_one_div

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by
  simpa [one_div] using inv_le_inv_of_neg ha hb
#align one_div_le_one_div_of_neg one_div_le_one_div_of_neg

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
  lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)
#align one_div_lt_one_div_of_neg one_div_lt_one_div_of_neg

theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
  suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2
#align one_div_lt_neg_one one_div_lt_neg_one

theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
  suffices 1 / a ≤ 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2
#align one_div_le_neg_one one_div_le_neg_one

/-! ### Results about halving -/


theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
  suffices a / 2 + a / 2 - a / 2 = a / 2 by rwa [add_halves] at this
  rw [add_sub_cancel_right]
#align sub_self_div_two sub_self_div_two

theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
  suffices a / 2 - (a / 2 + a / 2) = -(a / 2) by rwa [add_halves] at this
  rw [sub_add_eq_sub_sub, sub_self, zero_sub]
#align div_two_sub_self div_two_sub_self

theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two, div_lt_div_right (zero_lt_two' α)]
#align add_sub_div_two_lt add_sub_div_two_lt

/-- An inequality involving `2`. -/
theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 := by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_le_inv_of_le (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert (one_div a).le.trans (inv_le_inv_of_le zero_lt_two a2) using 1
  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add, ← two_mul, mul_inv_cancel two_ne_zero]
#align sub_one_div_inv_le_two sub_one_div_inv_le_two

/-! ### Results about `IsLUB` -/


-- TODO: Generalize to `LinearOrderedSemifield`
theorem IsLUB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isLUB_singleton
#align is_lub.mul_left IsLUB.mul_left

-- TODO: Generalize to `LinearOrderedSemifield`
theorem IsLUB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha
#align is_lub.mul_right IsLUB.mul_right

/-! ### Miscellaneous lemmas -/


theorem mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
    (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]
#align mul_sub_mul_div_mul_neg_iff mul_sub_mul_div_mul_neg_iff

theorem mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
    (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]
#align mul_sub_mul_div_mul_nonpos_iff mul_sub_mul_div_mul_nonpos_iff

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff
#align mul_sub_mul_div_mul_neg mul_sub_mul_div_mul_neg
#align div_lt_div_of_mul_sub_mul_div_neg div_lt_div_of_mul_sub_mul_div_neg

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff
#align div_le_div_of_mul_sub_mul_div_nonpos div_le_div_of_mul_sub_mul_div_nonpos
#align mul_sub_mul_div_mul_nonpos mul_sub_mul_div_mul_nonpos

theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
  ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩
#align exists_add_lt_and_pos_of_lt exists_add_lt_and_pos_of_lt

theorem le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h
#align le_of_forall_sub_le le_of_forall_sub_le

theorem mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  mul_self_eq_mul_self_iff.trans <|
    or_iff_left_of_imp fun h => by
      subst a
      have : b = 0 := le_antisymm (neg_nonneg.1 a0) b0
      rw [this, neg_zero]
#align mul_self_inj_of_nonneg mul_self_inj_of_nonneg

theorem min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : min (a / c) (b / c) = max a b / c :=
  Eq.symm <| Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc
#align min_div_div_right_of_nonpos min_div_div_right_of_nonpos

theorem max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : max (a / c) (b / c) = min a b / c :=
  Eq.symm <| Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc
#align max_div_div_right_of_nonpos max_div_div_right_of_nonpos

theorem abs_inv (a : α) : |a⁻¹| = |a|⁻¹ :=
  map_inv₀ (absHom : α →*₀ α) a
#align abs_inv abs_inv

theorem abs_div (a b : α) : |a / b| = |a| / |b| :=
  map_div₀ (absHom : α →*₀ α) a b
#align abs_div abs_div

theorem abs_one_div (a : α) : |1 / a| = 1 / |a| := by rw [abs_div, abs_one]
#align abs_one_div abs_one_div

end

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section LinearOrderedSemifield
variable {α : Type*} [LinearOrderedSemifield α] {a b : α}

private lemma div_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  div_nonneg ha.le hb

private lemma div_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  div_nonneg ha hb.le

private lemma div_ne_zero_of_pos_of_ne_zero (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 :=
  div_ne_zero ha.ne' hb

private lemma div_ne_zero_of_ne_zero_of_pos (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 :=
  div_ne_zero ha hb.ne'

private lemma zpow_zero_pos (a : α) : 0 < a ^ (0 : ℤ) := zero_lt_one.trans_eq (zpow_zero a).symm

end LinearOrderedSemifield

/-- The `positivity` extension which identifies expressions of the form `a / b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ / _] def evalDiv : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not /"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  let _a ← synthInstanceQ (q(LinearOrderedSemifield $α) : Q(Type u))
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(HDiv.hDiv)
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb => pure (.positive q(div_pos $pa $pb))
  | .positive pa, .nonnegative pb => pure (.nonnegative q(div_nonneg_of_pos_of_nonneg $pa $pb))
  | .nonnegative pa, .positive pb => pure (.nonnegative q(div_nonneg_of_nonneg_of_pos $pa $pb))
  | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(div_nonneg $pa $pb))
  | .positive pa, .nonzero pb => pure (.nonzero q(div_ne_zero_of_pos_of_ne_zero $pa $pb))
  | .nonzero pa, .positive pb => pure (.nonzero q(div_ne_zero_of_ne_zero_of_pos $pa $pb))
  | .nonzero pa, .nonzero pb => pure (.nonzero q(div_ne_zero $pa $pb))
  | _, _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a⁻¹`,
such that `positivity` successfully recognises `a`. -/
@[positivity _⁻¹]
def evalInv : PositivityExt where eval {u α} zα pα e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← withReducible (whnf e) | throwError "not ⁻¹"
  let _e_eq : $e =Q $f $a := ⟨⟩
  let _a ← synthInstanceQ (q(LinearOrderedSemifield $α) : Q(Type u))
  assumeInstancesCommute
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(Inv.inv)
  let ra ← core zα pα a
  match ra with
  | .positive pa => pure (.positive q(inv_pos_of_pos $pa))
  | .nonnegative pa => pure (.nonnegative q(inv_nonneg_of_nonneg $pa))
  | .nonzero pa => pure (.nonzero q(inv_ne_zero $pa))
  | .none => pure .none

/-- The `positivity` extension which identifies expressions of the form `a ^ (0:ℤ)`. -/
@[positivity _ ^ (0:ℤ), Pow.pow _ (0:ℤ)]
def evalPowZeroInt : PositivityExt where eval {u α} _zα _pα e := do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  _ ← synthInstanceQ (q(LinearOrderedSemifield $α) : Q(Type u))
  pure (.positive (q(zpow_zero_pos $a) : Expr))

end Mathlib.Meta.Positivity
