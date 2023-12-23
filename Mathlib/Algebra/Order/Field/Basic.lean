/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

#align_import algebra.order.field.basic from "leanprover-community/mathlib"@"84771a9f5f0bd5e5d6218811556508ddf476dcbd"

/-!
# Lemmas about linear ordered (semi)fields
-/


open Function OrderDual

variable {ι α β : Type*}

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] [ZeroLEOneClass α] {a b c d e : α} {m n : ℤ}

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

theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
    (hc : 0 ≤ c) : Monotone fun x => f x / c := by
  haveI := @LinearOrder.decidableLE α _
  simpa only [div_eq_mul_inv] using (monotone_mul_right_of_nonneg (inv_nonneg.2 hc)).comp hf
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
        _ < (a₁ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_left h _)
        ,
      calc
        (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := div_lt_div_of_lt zero_lt_two (add_lt_add_right h _)
        _ = a₂ := add_self_div_two a₂
        ⟩
#align linear_ordered_field.to_densely_ordered LinearOrderedSemiField.toDenselyOrdered

theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c :=
  Eq.symm <| Monotone.map_min fun _ _ => div_le_div_of_le hc
#align min_div_div_right min_div_div_right

theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c :=
  Eq.symm <| Monotone.map_max fun _ _ => div_le_div_of_le hc
#align max_div_div_right max_div_div_right

theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) :=
  fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy
#align one_div_strict_anti_on one_div_strictAntiOn

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
    1 / a ^ n ≤ 1 / a ^ m := by
  refine' (one_div_le_one_div _ _).mpr (pow_le_pow_right a1 mn) <;>
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
  ⟨fun h => div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le, fun h =>
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
  rw [add_sub_cancel]
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
  refine' (inv_le_inv_of_le (inv_pos.2 <| zero_lt_two' α) _).trans_eq (inv_inv (2 : α))
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

/-! ### Miscellaneous lemmmas -/


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
