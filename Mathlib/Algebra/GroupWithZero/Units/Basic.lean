/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Nat.Basic  -- shake: keep (non-recorded `nontrivial` dependency?)
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

We also define `Ring.inverse`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which inverts units and sends non-units to zero.
-/

@[expose] public section

assert_not_exists DenselyOrdered Equiv Subtype.restrict Multiplicative Ring

variable {α M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

end Units

namespace IsUnit

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one

namespace Ring

open Classical in
/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `Ring` namespace for brevity, it requires the weaker assumption
`MonoidWithZero M₀` instead of `Ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

@[inherit_doc]
scoped postfix:max "⁻¹ʳ" => inverse

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
theorem inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ) := by
  rw [inverse, dif_pos u.isUnit, IsUnit.unit_of_val_units]

theorem inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀) := dif_pos h

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ = 0 :=
  dif_neg h

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * x⁻¹ʳ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]

theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻¹ʳ * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]

theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * x⁻¹ʳ = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_one]

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * x⁻¹ʳ * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]

theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (x⁻¹ʳ * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mul]

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : x⁻¹ʳ * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩

theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variable (M₀) in
@[simp, grind =]
theorem inverse_one : (1 : M₀)⁻¹ʳ = 1 :=
  inverse_unit 1

variable (M₀) in
@[simp, grind =]
theorem inverse_zero : (0 : M₀)⁻¹ʳ = 0 := by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero

@[grind =]
theorem inverse_inverse {a : M₀} (h : IsUnit a) : inverse (inverse a) = a := by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit, inverse_unit, inv_inv]

end Ring

open scoped Ring

theorem IsUnit.ringInverse {a : M₀} : IsUnit a → IsUnit a⁻¹ʳ
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp, grind =]
theorem isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

@[grind =]
theorem Ring.inverse_mul {a b : M₀} (h : IsUnit a ∨ IsUnit b) : (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
    simp [Ring.inverse_non_unit, ha, this]
  · simp [Ring.inverse_of_isUnit, ha, hb, ha.mul hb, ← Units.val_mul, ← mul_inv_rev]
    simp

theorem Ring.isUnit_iff_inverse_ne_zero [Nontrivial M₀] {x : M₀} : IsUnit x ↔ x⁻¹ʳ ≠ 0 :=
 ⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt <| Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ

theorem Ring.not_isUnit_iff_inverse_eq_zero [Nontrivial M₀] {x : M₀} : ¬ IsUnit x ↔ x⁻¹ʳ = 0 := by
  grind

theorem Ring.isUnit_iff_mul_inverse_cancel {x : M₀} : IsUnit x ↔ x * x⁻¹ʳ = 1 := by
  nontriviality M₀
  refine ⟨mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ

theorem Ring.isUnit_iff_inverse_mul_cancel (x : M₀) : IsUnit x ↔ x⁻¹ʳ * x = 1 := by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

@[grind =]
theorem Ring.inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ = a := by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit, inverse_unit, inv_inv]

@[simp, grind =]
theorem Ring.inverse_inverse_inverse {a : M₀} : a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ := by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

namespace Units

variable [GroupWithZero G₀]

/-- Embed a non-zero element of a `GroupWithZero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
theorem val_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl

@[simp]
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl

theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel₀ u.ne_zero

theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel₀ u.ne_zero

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]
theorem exists_iff_ne_zero {p : G₀ → Prop} : (∃ u : G₀ˣ, p u) ↔ ∃ x ≠ 0, p x := by
  simp [exists0]

theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  simpa using em _

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).isUnit

@[simp]
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := @fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `NoZeroDivisors` instance, which depends on `mk0`.
@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl

theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]

theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.not.trans not_or

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.isUnit.div_self

@[simp]
lemma div_self_eq_one₀ : a / a = 1 ↔ a ≠ 0 where
  mp := by contrapose!; simp +contextual
  mpr := div_self

lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.isUnit.eq_mul_inv_iff_mul_eq

lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.isUnit.eq_inv_mul_iff_mul_eq

lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.isUnit.inv_mul_eq_iff_eq_mul

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.isUnit.mul_inv_eq_iff_eq_mul

lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := hb.isUnit.mul_inv_eq_one

lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := ha.isUnit.inv_mul_eq_one

lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := hb.isUnit.mul_eq_one_iff_eq_inv

lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.isUnit.mul_eq_one_iff_inv_eq

/-- A variant of `eq_mul_inv_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
lemma mul_eq_of_eq_mul_inv₀ (ha : a ≠ 0) (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

/-- A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
lemma mul_eq_of_eq_inv_mul₀ (hb : b ≠ 0) (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h

/-- A variant of `inv_mul_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
lemma eq_mul_of_inv_mul_eq₀ (hc : c ≠ 0) (h : b⁻¹ * a = c) : a = b * c :=
  (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

/-- A variant of `mul_inv_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
lemma eq_mul_of_mul_inv_eq₀ (hb : b ≠ 0) (h : a * c⁻¹ = b) : a = b * c :=
  (mul_eq_of_eq_mul_inv₀ hb h.symm).symm

lemma div_mul_cancel₀ (a : G₀) (h : b ≠ 0) : a / b * b = a := by simp [h]

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel

lemma one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 := h.isUnit.one_div_mul_cancel

@[simp]
lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj

lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff

lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff

-- TODO: Swap RHS around
lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := hb.isUnit.div_eq_iff.trans eq_comm

lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := hc.isUnit.eq_div_iff

lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.isUnit.div_eq_of_eq_mul

lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.isUnit.eq_div_of_mul_eq

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq

lemma div_mul_cancel_right₀ (hb : b ≠ 0) (a : G₀) : b / (a * b) = a⁻¹ :=
  hb.isUnit.div_mul_cancel_right _

lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  hc.isUnit.mul_div_mul_right _ _

-- TODO: Duplicate of `mul_inv_cancel_right₀`
lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.isUnit.mul_mul_div _).symm

lemma div_div_div_cancel_right₀ (hc : c ≠ 0) (a b : G₀) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ hc]

lemma div_mul_div_cancel₀ (hb : b ≠ 0) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel₀ _ hb]

lemma div_mul_cancel_of_imp (h : b = 0 → a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

lemma mul_div_cancel_of_imp (h : b = 0 → a = 0) : a * b / b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

@[simp] lemma divp_mk0 (a : G₀) (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b := divp_eq_div _ _

lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

lemma pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
  · exact pow_sub₀ _ ha <| Nat.le_of_lt h

lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]

lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]

lemma zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]

lemma zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa using zpow_sub₀ ha m n

lemma zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa using zpow_sub₀ ha n 1

lemma zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa using zpow_sub₀ ha 1 n

lemma zpow_ne_zero {a : G₀} : ∀ n : ℤ, a ≠ 0 → a ^ n ≠ 0
  | (_ : ℕ) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha ↦ by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)

lemma eq_zero_of_zpow_eq_zero {n : ℤ} : a ^ n = 0 → a = 0 := not_imp_not.1 (zpow_ne_zero _)

lemma zpow_eq_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩

lemma zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (zpow_eq_zero_iff hn).ne

lemma zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

@[grind =]
theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid :
    DivisionCommMonoid G₀ where
  __ := ‹CommGroupWithZero G₀›
  __ := GroupWithZero.toDivisionMonoid

lemma div_mul_cancel_left₀ (ha : a ≠ 0) (b : G₀) : a / (a * b) = b⁻¹ :=
  ha.isUnit.div_mul_cancel_left _

lemma mul_div_cancel_left_of_imp (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]

lemma mul_div_cancel_of_imp' (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]

lemma mul_div_cancel₀ (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.isUnit.mul_div_cancel _

lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  hc.isUnit.mul_div_mul_left _ _

lemma mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel₀ _ hd]

lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.isUnit.div_eq_div_iff hd.isUnit

lemma mul_inv_eq_mul_inv_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit

lemma inv_mul_eq_inv_mul_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b :=
  hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

/-- The `CommGroupWithZero` version of `div_eq_div_iff_div_eq_div`. -/
lemma div_eq_div_iff_div_eq_div' (hb : b ≠ 0) (hc : c ≠ 0) : a / b = c / d ↔ a / c = b / d := by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c, div_mul_eq_mul_div, mul_div_assoc]

lemma div_eq_div_of_div_eq_div (hc : c ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) : a / c = b / d :=
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h

@[simp] lemma div_div_cancel₀ (ha : a ≠ 0) : a / (a / b) = b := ha.isUnit.div_div_cancel

lemma div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := ha.isUnit.div_div_cancel_left

lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_cancel_left₀ h, one_div]

lemma div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq, mul_comm, mul_div_mul_right _ _ hc]

@[simp] lemma div_mul_div_cancel₀' (ha : a ≠ 0) (b c : G₀) : a / b * (c / a) = c / b := by
  rw [mul_comm, div_mul_div_cancel₀ ha]

end CommGroupWithZero

section NoncomputableDefs

variable {M : Type*} [Nontrivial M]

open Classical in
/-- Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0. -/
@[implicit_reducible]
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec] }

/-- Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
@[implicit_reducible]
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs
