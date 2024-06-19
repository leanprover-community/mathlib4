/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists

#align_import algebra.group_with_zero.units.basic from "leanprover-community/mathlib"@"df5e9937a06fdd349fc60106f54b84d47b1434f0"

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

We also define `Ring.inverse`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which inverts units and sends non-units to zero.
-/

-- Guard against import creep
assert_not_exists Multiplicative
assert_not_exists DenselyOrdered

variable {α M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv
#align units.ne_zero Units.ne_zero

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩
#align units.mul_left_eq_zero Units.mul_left_eq_zero

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩
#align units.mul_right_eq_zero Units.mul_right_eq_zero

end Units

namespace IsUnit

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero
#align is_unit.ne_zero IsUnit.ne_zero

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero
#align is_unit.mul_right_eq_zero IsUnit.mul_right_eq_zero

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero
#align is_unit.mul_left_eq_zero IsUnit.mul_left_eq_zero

end IsUnit

@[simp]
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩
#align is_unit_zero_iff isUnit_zero_iff

-- Porting note: removed `simp` tag because `simpNF` says it's redundant
theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one
#align not_is_unit_zero not_isUnit_zero

namespace Ring

open scoped Classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `Ring` namespace for brevity, it requires the weaker assumption
`MonoidWithZero M₀` instead of `Ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0
#align ring.inverse Ring.inverse

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp]
theorem inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) := by
  rw [inverse, dif_pos u.isUnit, IsUnit.unit_of_val_units]
#align ring.inverse_unit Ring.inverse_unit

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : inverse x = 0 :=
  dif_neg h
#align ring.inverse_non_unit Ring.inverse_non_unit

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * inverse x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]
#align ring.mul_inverse_cancel Ring.mul_inverse_cancel

theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : inverse x * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]
#align ring.inverse_mul_cancel Ring.inverse_mul_cancel

theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * inverse x = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_one]
#align ring.mul_inverse_cancel_right Ring.mul_inverse_cancel_right

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * inverse x * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]
#align ring.inverse_mul_cancel_right Ring.inverse_mul_cancel_right

theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (inverse x * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mul]
#align ring.mul_inverse_cancel_left Ring.mul_inverse_cancel_left

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : inverse x * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]
#align ring.inverse_mul_cancel_left Ring.inverse_mul_cancel_left

theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : inverse x * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩
#align ring.inverse_mul_eq_iff_eq_mul Ring.inverse_mul_eq_iff_eq_mul

theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * inverse z ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩
#align ring.eq_mul_inverse_iff_mul_eq Ring.eq_mul_inverse_iff_mul_eq

variable (M₀)

@[simp]
theorem inverse_one : inverse (1 : M₀) = 1 :=
  inverse_unit 1
#align ring.inverse_one Ring.inverse_one

@[simp]
theorem inverse_zero : inverse (0 : M₀) = 0 := by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero
#align ring.inverse_zero Ring.inverse_zero

variable {M₀}

end Ring

theorem IsUnit.ring_inverse {a : M₀} : IsUnit a → IsUnit (Ring.inverse a)
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩
#align is_unit.ring_inverse IsUnit.ring_inverse

@[simp]
theorem isUnit_ring_inverse {a : M₀} : IsUnit (Ring.inverse a) ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero
      ,
    IsUnit.ring_inverse⟩
#align is_unit_ring_inverse isUnit_ring_inverse

namespace Units

variable [GroupWithZero G₀]
variable {a b : G₀}

/-- Embed a non-zero element of a `GroupWithZero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩
#align units.mk0 Units.mk0

@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl
#align units.mk0_one Units.mk0_one

@[simp]
theorem val_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl
#align units.coe_mk0 Units.val_mk0

@[simp]
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl
#align units.mk0_coe Units.mk0_val

-- Porting note: removed `simp` tag because `simpNF` says it's redundant
theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel u.ne_zero
#align units.mul_inv' Units.mul_inv'

-- Porting note: removed `simp` tag because `simpNF` says it's redundant
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel u.ne_zero
#align units.inv_mul' Units.inv_mul'

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩
#align units.mk0_inj Units.mk0_inj

/-- In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩
#align units.exists0 Units.exists0

/-- An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  Iff.trans (by simp_rw [val_mk0]) exists0.symm
  -- Porting note: had to add the `rfl`
#align units.exists0' Units.exists0'

@[simp]
theorem exists_iff_ne_zero {p : G₀ → Prop} : (∃ u : G₀ˣ, p u) ↔ ∃ x ≠ 0, p x := by
  simp [exists0]
#align units.exists_iff_ne_zero Units.exists_iff_ne_zero

theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  simpa using em _
#align group_with_zero.eq_zero_or_unit GroupWithZero.eq_zero_or_unit

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c d : G₀} {m n : ℕ}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).isUnit
#align is_unit.mk0 IsUnit.mk0

@[simp]
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)
#align is_unit_iff_ne_zero isUnit_iff_ne_zero

alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero
#align ne.is_unit Ne.isUnit

-- Porting note: can't add this attribute?
-- https://github.com/leanprover-community/mathlib4/issues/740
-- attribute [protected] Ne.is_unit

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := @fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }
#align group_with_zero.no_zero_divisors GroupWithZero.noZeroDivisors

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `NoZeroDivisors` instance, which depends on `mk0`.
@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl
#align units.mk0_mul Units.mk0_mul

theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)
#align div_ne_zero div_ne_zero

@[simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]
#align div_eq_zero_iff div_eq_zero_iff

theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.not.trans not_or
#align div_ne_zero_iff div_ne_zero_iff

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.isUnit.div_self
#align div_self div_self

lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.isUnit.eq_mul_inv_iff_mul_eq
#align eq_mul_inv_iff_mul_eq₀ eq_mul_inv_iff_mul_eq₀

lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.isUnit.eq_inv_mul_iff_mul_eq
#align eq_inv_mul_iff_mul_eq₀ eq_inv_mul_iff_mul_eq₀

lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.isUnit.inv_mul_eq_iff_eq_mul
#align inv_mul_eq_iff_eq_mul₀ inv_mul_eq_iff_eq_mul₀

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.isUnit.mul_inv_eq_iff_eq_mul
#align mul_inv_eq_iff_eq_mul₀ mul_inv_eq_iff_eq_mul₀

lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := hb.isUnit.mul_inv_eq_one
#align mul_inv_eq_one₀ mul_inv_eq_one₀

lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := ha.isUnit.inv_mul_eq_one
#align inv_mul_eq_one₀ inv_mul_eq_one₀

lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := hb.isUnit.mul_eq_one_iff_eq_inv
#align mul_eq_one_iff_eq_inv₀ mul_eq_one_iff_eq_inv₀

lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.isUnit.mul_eq_one_iff_inv_eq
#align mul_eq_one_iff_inv_eq₀ mul_eq_one_iff_inv_eq₀

/-- A variant of `eq_mul_inv_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
lemma mul_eq_of_eq_mul_inv₀ (ha : a ≠ 0) (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

/-- A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
lemma mul_eq_of_eq_inv_mul₀ (hb : b ≠ 0) (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h

/-- A variant of `inv_mul_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
lemma eq_mul_of_inv_mul_eq₀ (hc : c ≠ 0) (h : b⁻¹ * a = c) : a = b * c := by
  rwa [← inv_mul_eq_iff_eq_mul₀]; rintro rfl; simp [hc.symm] at h

/-- A variant of `mul_inv_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
lemma eq_mul_of_mul_inv_eq₀ (hb : b ≠ 0) (h : a * c⁻¹ = b) : a = b * c := by
  rwa [← mul_inv_eq_iff_eq_mul₀]; rintro rfl; simp [hb.symm] at h

@[simp] lemma div_mul_cancel₀ (a : G₀) (h : b ≠ 0) : a / b * b = a := h.isUnit.div_mul_cancel _
#align div_mul_cancel div_mul_cancel₀

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel
#align mul_one_div_cancel mul_one_div_cancel

lemma one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 := h.isUnit.one_div_mul_cancel
#align one_div_mul_cancel one_div_mul_cancel

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj
#align div_left_inj' div_left_inj'

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff
#align div_eq_iff div_eq_iff

@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff
#align eq_div_iff eq_div_iff

-- TODO: Swap RHS around
lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := hb.isUnit.div_eq_iff.trans eq_comm
#align div_eq_iff_mul_eq div_eq_iff_mul_eq

lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := hc.isUnit.eq_div_iff
#align eq_div_iff_mul_eq eq_div_iff_mul_eq

lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.isUnit.div_eq_of_eq_mul
#align div_eq_of_eq_mul div_eq_of_eq_mul

lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.isUnit.eq_div_of_mul_eq
#align eq_div_of_mul_eq eq_div_of_mul_eq

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq
#align div_eq_one_iff_eq div_eq_one_iff_eq

lemma div_mul_cancel_right₀ (hb : b ≠ 0) (a : G₀) : b / (a * b) = a⁻¹ :=
  hb.isUnit.div_mul_cancel_right _

set_option linter.deprecated false in
@[deprecated div_mul_cancel_right₀] -- 2024-03-20
lemma div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a := hb.isUnit.div_mul_left
#align div_mul_left div_mul_left

lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  hc.isUnit.mul_div_mul_right _ _
#align mul_div_mul_right mul_div_mul_right

-- TODO: Duplicate of `mul_inv_cancel_right₀`
lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.isUnit.mul_mul_div _).symm
#align mul_mul_div mul_mul_div

lemma div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ hc]
#align div_div_div_cancel_right div_div_div_cancel_right

lemma div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : a / c * (c / b) = a / b := by
  rw [← mul_div_assoc, div_mul_cancel₀ _ hc]
#align div_mul_div_cancel div_mul_div_cancel

lemma div_mul_cancel_of_imp (h : b = 0 → a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;>  simp [*]
#align div_mul_cancel_of_imp div_mul_cancel_of_imp

lemma mul_div_cancel_of_imp (h : b = 0 → a = 0) : a * b / b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;>  simp [*]
#align mul_div_cancel_of_imp mul_div_cancel_of_imp

@[simp] lemma divp_mk0 (a : G₀) (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b := divp_eq_div _ _
#align divp_mk0 divp_mk0

lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2
#align pow_sub₀ pow_sub₀

lemma pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by omega), zero_mul]
  · exact pow_sub₀ _ ha <| Nat.le_of_lt h
#align pow_sub_of_lt pow_sub_of_lt

lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub₀ inv_pow_sub₀

lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub_of_lt inv_pow_sub_of_lt

lemma zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]
#align zpow_sub₀ zpow_sub₀

lemma zpow_ne_zero {a : G₀} : ∀ n : ℤ, a ≠ 0 → a ^ n ≠ 0
  | (_ : ℕ) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha ↦ by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)
#align zpow_ne_zero_of_ne_zero zpow_ne_zero
#align zpow_ne_zero zpow_ne_zero

lemma eq_zero_of_zpow_eq_zero {n : ℤ} : a ^ n = 0 → a = 0 := not_imp_not.1 (zpow_ne_zero _)
#align zpow_eq_zero eq_zero_of_zpow_eq_zero

@[deprecated (since := "2024-05-07")] alias zpow_ne_zero_of_ne_zero := zpow_ne_zero
@[deprecated (since := "2024-05-07")] alias zpow_eq_zero := eq_zero_of_zpow_eq_zero

lemma zpow_eq_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩
#align zpow_eq_zero_iff zpow_eq_zero_iff

lemma zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (zpow_eq_zero_iff hn).ne

lemma zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel (zpow_ne_zero n ha)
#align zpow_neg_mul_zpow_self zpow_neg_mul_zpow_self

theorem Ring.inverse_eq_inv (a : G₀) : Ring.inverse a = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)
#align ring.inverse_eq_inv Ring.inverse_eq_inv

@[simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv
#align ring.inverse_eq_inv' Ring.inverse_eq_inv'

/-- In a `GroupWithZero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps] def unitsEquivNeZero [GroupWithZero α] : αˣ ≃ {a : α // a ≠ 0} where
  toFun a := ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop
  left_inv _ := Units.ext rfl
  right_inv _ := rfl
#align units_equiv_ne_zero unitsEquivNeZero
#align units_equiv_ne_zero_apply_coe unitsEquivNeZero_apply_coe
#align units_equiv_ne_zero_symm_apply unitsEquivNeZero_symm_apply

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- see Note [lower instance priority]
instance (priority := 10) CommGroupWithZero.toCancelCommMonoidWithZero :
    CancelCommMonoidWithZero G₀ :=
  { GroupWithZero.toCancelMonoidWithZero,
    CommGroupWithZero.toCommMonoidWithZero with }
#align comm_group_with_zero.to_cancel_comm_monoid_with_zero CommGroupWithZero.toCancelCommMonoidWithZero

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid :
    DivisionCommMonoid G₀ where
  __ := ‹CommGroupWithZero G₀›
  __ := GroupWithZero.toDivisionMonoid
#align comm_group_with_zero.to_division_comm_monoid CommGroupWithZero.toDivisionCommMonoid

lemma div_mul_cancel_left₀ (ha : a ≠ 0) (b : G₀) : a / (a * b) = b⁻¹ :=
  ha.isUnit.div_mul_cancel_left _

set_option linter.deprecated false in
@[deprecated div_mul_cancel_left₀] -- 2024-03-22
lemma div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b := ha.isUnit.div_mul_right _
#align div_mul_right div_mul_right

lemma mul_div_cancel_left_of_imp (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]
#align mul_div_cancel_left_of_imp mul_div_cancel_left_of_imp

lemma mul_div_cancel_of_imp' (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]
#align mul_div_cancel_of_imp' mul_div_cancel_of_imp'

lemma mul_div_cancel₀ (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.isUnit.mul_div_cancel _
#align mul_div_cancel' mul_div_cancel₀

lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  hc.isUnit.mul_div_mul_left _ _
#align mul_div_mul_left mul_div_mul_left

lemma mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel₀ _ hd]
#align mul_eq_mul_of_div_eq_div mul_eq_mul_of_div_eq_div

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.isUnit.div_eq_div_iff hd.isUnit
#align div_eq_div_iff div_eq_div_iff

/-- The `CommGroupWithZero` version of `div_eq_div_iff_div_eq_div`. -/
lemma div_eq_div_iff_div_eq_div' (hb : b ≠ 0) (hc : c ≠ 0) : a / b = c / d ↔ a / c = b / d := by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c, div_mul_eq_mul_div, mul_div_assoc]

lemma div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b := ha.isUnit.div_div_cancel
#align div_div_cancel' div_div_cancel'

lemma div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := ha.isUnit.div_div_cancel_left
#align div_div_cancel_left' div_div_cancel_left'

lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_cancel_left₀ h, one_div]
#align div_helper div_helper

lemma div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq, mul_comm, mul_div_mul_right _ _ hc]

end CommGroupWithZero

section NoncomputableDefs

open scoped Classical

variable {M : Type*} [Nontrivial M]

/-- Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }
#align group_with_zero_of_is_unit_or_eq_zero groupWithZeroOfIsUnitOrEqZero

/-- Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }
#align comm_group_with_zero_of_is_unit_or_eq_zero commGroupWithZeroOfIsUnitOrEqZero

end NoncomputableDefs

-- 2024-03-20
-- The names `div_mul_cancel`, `mul_div_cancel` and `mul_div_cancel_left` have been reused
-- @[deprecated] alias div_mul_cancel := div_mul_cancel₀
-- @[deprecated] alias mul_div_cancel := mul_div_cancel_right₀
-- @[deprecated] alias mul_div_cancel_left := mul_div_cancel_left₀
@[deprecated] alias mul_div_cancel' := mul_div_cancel₀
