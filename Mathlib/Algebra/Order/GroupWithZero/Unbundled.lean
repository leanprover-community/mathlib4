/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.MonoidWithZero.Unbundled

/-!
# Monotonicity of multiplication by positive elements in groups with zero
-/

open Function

variable {G₀ : Type*}

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀]

/-- See `div_self` for the version with equality when `a ≠ 0`. -/
lemma div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀] {a b c : G₀}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  fun a ha ↦ flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

lemma div_pos [PosMulStrictMono G₀] (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

lemma div_nonneg [PosMulMono G₀] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg [MulPosMono G₀] (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

lemma zpow_nonneg [PosMulMono G₀] (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

lemma zpow_pos [PosMulStrictMono G₀] (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _

@[deprecated (since := "2024-10-08")] alias zpow_pos_of_pos := zpow_pos

section PosMulMono
variable [PosMulMono G₀] {m n : ℤ}

/-- See `le_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

/-- See `inv_mul_le_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]

/-- See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← inv_mul_le_iff₀ ha, mul_one]

lemma one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

@[bound]
lemma inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 := (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

lemma one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

/-- One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/-- One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

@[bound]
lemma inv_mul_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 :=
  inv_mul_le_of_le_mul₀ hb zero_le_one <| by rwa [mul_one]

lemma zpow_right_mono₀ (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

@[gcongr]
lemma zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn

@[gcongr]
lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a ^ n ≤ a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn

lemma one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn

lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

lemma zpow_le_one_of_nonpos₀ (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 := by
  simpa using zpow_right_mono₀ ha hn

lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : n ≤ 0) : 1 ≤ a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

end PosMulMono

section MulPosMono
variable [MulPosMono G₀]

/-- See `le_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)

/-- See `mul_inv_le_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)

/-- See `le_div_iff₀'` for a version with multiplication on the other side. -/
lemma le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

/-- See `div_le_iff₀'` for a version with multiplication on the other side. -/
lemma div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

lemma one_le_div₀ (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]
lemma div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]

/-- One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/-- One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/-- One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative). -/
lemma mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/-- One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative). -/
lemma div_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
lemma mul_inv_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[bound]
lemma div_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[mono, gcongr, bound]
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonneg_right hab (one_div_nonneg.2 hc)

variable [PosMulMono G₀]

/-- See `inv_anti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [inv_le_iff_one_le_mul₀' ha, le_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

/-- See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumption. -/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

/-- See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumption. -/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
@[gcongr]
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (hc.trans_le h) hc).mpr h) ha

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] {m n : ℤ}

/-- See `lt_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h (inv_pos.2 hc)

/-- See `inv_mul_lt_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h (inv_pos.2 hc)

/-- See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

@[bound]
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn

@[gcongr]
lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn

lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn

lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn

lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono₀ ha).le_iff_le

@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt

lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m ≤ a ^ n ↔ n ≤ m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_le

lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_lt

@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 ≤ a ^ n ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 ≤ a ^ n ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end PosMulStrictMono

section MulPosStrictMono
variable [MulPosStrictMono G₀]

/-- See `lt_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h (inv_pos.2 hc)

/-- See `mul_inv_lt_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h (inv_pos.2 hc)

/-- See `lt_div_iff₀'` for a version with multiplication on the other side. -/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

/-- See `div_lt_iff₀'` for a version with multiplication on the other side. -/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]

/-- See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha, one_mul]

@[gcongr, bound]
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)

variable [PosMulStrictMono G₀]

/-- See `inv_strictAnti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha, lt_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba

/-- See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumption. -/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/-- See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumption. -/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

@[gcongr, bound]
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (hc.trans h) hc).2 h) ha

end MulPosStrictMono
end PartialOrder

section LinearOrder
variable [LinearOrder G₀] [ZeroLEOneClass G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_lt h

lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 ≤ b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha ↦ (div_nonneg ha hb).not_lt h

end PosMulMono

variable [PosMulStrictMono G₀] {m n : ℤ}

lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

lemma inv_le_one_iff₀ : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_lt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff

lemma zpow_eq_one_iff_right₀ (ha₀ : 0 ≤ a) (ha₁ : a ≠ 1) {n : ℤ} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

variable [MulPosStrictMono G₀]

lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b where
  mp := le_imp_le_of_lt_imp_lt fun hab ↦ div_lt_div_of_pos_right hab hc
  mpr hab := div_le_div_of_nonneg_right hab hc.le

lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| div_le_div_iff_of_pos_right hc

lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b < a / c ↔ c < b := by simp only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv₀ hb hc]

lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (div_lt_div_iff_of_pos_left ha hc hb)

@[mono, gcongr, bound]
lemma div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hac ((inv_le_inv₀ (hd.trans_le hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb) hc

@[gcongr]
lemma div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul hac ((inv_le_inv₀ (hd.trans_le hdb) hd).2 hdb) (inv_pos.2 <| hd.trans_le hdb) hc

lemma div_lt_div₀' (hac : a ≤ c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end GroupWithZero.LinearOrder

section CommSemigroupHasZero

variable {α : Type*} [Mul α] [@Std.Commutative α (· * ·)] [Zero α] [Preorder α]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [posMulStrictMono_iff, mulPosStrictMono_iff, Std.Commutative.comm]

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [posMulReflectLT_iff, mulPosReflectLT_iff, Std.Commutative.comm]

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [posMulMono_iff, mulPosMono_iff, Std.Commutative.comm]

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [posMulReflectLE_iff, mulPosReflectLE_iff, Std.Commutative.comm]

end CommSemigroupHasZero

section CommGroupWithZero
variable [CommGroupWithZero G₀]
variable [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]

section PosMulMono
variable [PosMulMono G₀] {a b c d : G₀}

/-- See `le_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_le_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ a * c := by
  rw [inv_mul_le_iff₀ hc, mul_comm]

/-- See `le_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a ≤ b * c⁻¹ ↔ c * a ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_le_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [mul_inv_le_iff₀ hc, mul_comm]

lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hb, ← mul_div_right_comm, le_div_iff₀ hd]

/-- See `le_div_iff₀` for a version with multiplication on the other side. -/
lemma le_div_iff₀' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_div_iff₀ hc, mul_comm]

/-- See `div_le_iff₀` for a version with multiplication on the other side. -/
lemma div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hc, mul_comm]

lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_div_iff₀ ha, le_div_iff₀' hc]

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hb, div_le_iff₀' hc]

end PosMulMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] {a b c d : G₀}

/-- See `lt_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_lt_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- See `lt_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_lt_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [mul_inv_lt_iff₀ hc, mul_comm]

lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hb, ← mul_div_right_comm, lt_div_iff₀ hd]

/-- See `lt_div_iff₀` for a version with multiplication on the other side. -/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_div_iff₀ hc, mul_comm]

/-- See `div_lt_iff₀` for a version with multiplication on the other side. -/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hc, mul_comm]

lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_div_iff₀ ha, lt_div_iff₀' hc]

lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

end PosMulStrictMono
end CommGroupWithZero
