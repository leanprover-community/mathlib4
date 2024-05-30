/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Logic.Unique

#align_import algebra.group_with_zero.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `GroupWithZero` and `CommGroupWithZero`.
To reduce import dependencies, the type-classes themselves are in
`Algebra.GroupWithZero.Defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

assert_not_exists DenselyOrdered

open scoped Classical

open Function

variable {α M₀ G₀ M₀' G₀' F F' : Type*}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b
#align left_ne_zero_of_mul left_ne_zero_of_mul

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)
#align right_ne_zero_of_mul right_ne_zero_of_mul

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
#align ne_zero_and_ne_zero_of_mul ne_zero_and_ne_zero_of_mul

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 :=
  if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]
#align mul_eq_zero_of_ne_zero_imp_eq_zero mul_eq_zero_of_ne_zero_imp_eq_zero

/-- To match `one_mul_eq_id`. -/
theorem zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0 :=
  funext zero_mul
#align zero_mul_eq_const zero_mul_eq_const

/-- To match `mul_one_eq_id`. -/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero
#align mul_zero_eq_const mul_zero_eq_const

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id
#align eq_zero_of_mul_self_eq_zero eq_zero_of_mul_self_eq_zero

@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩
#align mul_ne_zero mul_ne_zero

end Mul

namespace NeZero

instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
    NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩

end NeZero

end

section

variable [MulZeroOneClass M₀]

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a, ← h, mul_zero]
#align eq_zero_of_zero_eq_one eq_zero_of_zero_eq_one

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h
#align unique_of_zero_eq_one uniqueOfZeroEqOne

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩
#align subsingleton_iff_zero_eq_one subsingleton_iff_zero_eq_one

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one
#align subsingleton_of_zero_eq_one subsingleton_of_zero_eq_one

theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b
#align eq_of_zero_eq_one eq_of_zero_eq_one

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one
#align zero_ne_one_or_forall_eq_0 zero_ne_one_or_forall_eq_0

end

section

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h
#align left_ne_zero_of_mul_eq_one left_ne_zero_of_mul_eq_one

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| ne_zero_of_eq_one h
#align right_ne_zero_of_mul_eq_one right_ne_zero_of_mul_eq_one

end

section MonoidWithZero
variable [MonoidWithZero M₀] {a : M₀} {m n : ℕ}

@[simp] lemma zero_pow : ∀ {n : ℕ}, n ≠ 0 → (0 : M₀) ^ n = 0
  | n + 1, _ => by rw [pow_succ, mul_zero]
#align zero_pow zero_pow
#align zero_pow' zero_pow

lemma zero_pow_eq (n : ℕ) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]
#align zero_pow_eq zero_pow_eq

lemma pow_eq_zero_of_le : ∀ {m n} (hmn : m ≤ n) (ha : a ^ m = 0), a ^ n = 0
  | _, _, Nat.le.refl, ha => ha
  | _, _, Nat.le.step hmn, ha => by rw [pow_succ, pow_eq_zero_of_le hmn ha, zero_mul]
#align pow_eq_zero_of_le pow_eq_zero_of_le

lemma ne_zero_pow (hn : n ≠ 0) (ha : a ^ n ≠ 0) : a ≠ 0 := by rintro rfl; exact ha $ zero_pow hn
#align ne_zero_pow ne_zero_pow

@[simp]
lemma zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n ≠ 0 :=
  ⟨by rintro h rfl; simp at h, zero_pow⟩
#align zero_pow_eq_zero zero_pow_eq_zero

variable [NoZeroDivisors M₀]

lemma pow_eq_zero : ∀ {n}, a ^ n = 0 → a = 0
  | 0, ha => by simpa using congr_arg (a * ·) ha
  | n + 1, ha => by rw [pow_succ, mul_eq_zero] at ha; exact ha.elim pow_eq_zero id
#align pow_eq_zero pow_eq_zero

@[simp] lemma pow_eq_zero_iff (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨pow_eq_zero, by rintro rfl; exact zero_pow hn⟩

#align pow_eq_zero_iff pow_eq_zero_iff

lemma pow_ne_zero_iff (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (pow_eq_zero_iff hn).not
#align pow_ne_zero_iff pow_ne_zero_iff

@[field_simps]
lemma pow_ne_zero (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 := mt pow_eq_zero h
#align pow_ne_zero pow_ne_zero

instance NeZero.pow [NeZero a] : NeZero (a ^ n) := ⟨pow_ne_zero n NeZero.out⟩
#align ne_zero.pow NeZero.pow

lemma sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff two_ne_zero
#align sq_eq_zero_iff sq_eq_zero_iff

@[simp] lemma pow_eq_zero_iff' [Nontrivial M₀] : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
#align pow_eq_zero_iff' pow_eq_zero_iff'

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_noZeroDivisors : NoZeroDivisors M₀ :=
  ⟨fun ab0 => or_iff_not_imp_left.mpr fun ha => mul_left_cancel₀ ha <|
    ab0.trans (mul_zero _).symm⟩
#align cancel_monoid_with_zero.to_no_zero_divisors CancelMonoidWithZero.to_noZeroDivisors

@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp only [hc, mul_zero, or_true]; simp [mul_left_inj', hc]]
#align mul_eq_mul_right_iff mul_eq_mul_right_iff

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]
#align mul_eq_mul_left_iff mul_eq_mul_left_iff

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
#align mul_right_eq_self₀ mul_right_eq_self₀

theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
#align mul_left_eq_self₀ mul_left_eq_self₀

@[simp]
theorem mul_eq_left₀ (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]
#align mul_eq_left₀ mul_eq_left₀

@[simp]
theorem mul_eq_right₀ (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]
#align mul_eq_right₀ mul_eq_right₀

@[simp]
theorem left_eq_mul₀ (ha : a ≠ 0) : a = a * b ↔ b = 1 := by rw [eq_comm, mul_eq_left₀ ha]
#align left_eq_mul₀ left_eq_mul₀

@[simp]
theorem right_eq_mul₀ (hb : b ≠ 0) : b = a * b ↔ a = 1 := by rw [eq_comm, mul_eq_right₀ hb]
#align right_eq_mul₀ right_eq_mul₀

/-- An element of a `CancelMonoidWithZero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  Classical.byContradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm
#align eq_zero_of_mul_eq_self_right eq_zero_of_mul_eq_self_right

/-- An element of a `CancelMonoidWithZero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  Classical.byContradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm
#align eq_zero_of_mul_eq_self_left eq_zero_of_mul_eq_self_left

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (fun y => x⁻¹ * y) w
#align group_with_zero.mul_left_injective GroupWithZero.mul_left_injective

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel h, mul_one] using congr_arg (fun y => y * x⁻¹) w
#align group_with_zero.mul_right_injective GroupWithZero.mul_right_injective

@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]
#align inv_mul_cancel_right₀ inv_mul_cancel_right₀


@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
#align inv_mul_cancel_left₀ inv_mul_cancel_left₀


private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZero G₀› with
    inv := Inv.inv,
    inv_inv := fun a => by
      by_cases h : a = 0
      · simp [h]
      · exact left_inv_eq_right_inv (inv_mul_cancel <| inv_ne_zero h) (inv_mul_cancel h)
        ,
    mul_inv_rev := fun a b => by
      by_cases ha : a = 0
      · simp [ha]
      by_cases hb : b = 0
      · simp [hb]
      apply inv_eq_of_mul
      simp [mul_assoc, ha, hb],
    inv_eq_of_mul := fun _ _ => inv_eq_of_mul }
#align group_with_zero.to_division_monoid GroupWithZero.toDivisionMonoid

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.toCancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZero G₀) with
    mul_left_cancel_of_ne_zero := @fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
    mul_right_cancel_of_ne_zero := @fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }
#align group_with_zero.to_cancel_monoid_with_zero GroupWithZero.toCancelMonoidWithZero

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]
#align zero_div zero_div

@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]
#align div_zero div_zero

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel h, mul_one]
#align mul_self_mul_inv mul_self_mul_inv


/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel h, one_mul]
#align mul_inv_mul_self mul_inv_mul_self


/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel h, one_mul]
#align inv_mul_mul_self inv_mul_mul_self


/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]
#align mul_self_div_self mul_self_div_self

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_self a]
#align div_self_mul_self div_self_mul_self

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _
#align div_self_mul_self' div_self_mul_self'


theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h
#align one_div_ne_zero one_div_ne_zero

@[simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_eq_inv, inv_zero]
#align inv_eq_zero inv_eq_zero

@[simp]
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm
#align zero_eq_inv zero_eq_inv

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a
#align div_div_self div_div_self

theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction
#align ne_zero_of_one_div_ne_zero ne_zero_of_one_div_ne_zero

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim
#align eq_zero_of_one_div_eq_zero eq_zero_of_one_div_eq_zero

theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel h]⟩
#align mul_left_surjective₀ mul_left_surjective₀

theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel h]⟩
#align mul_right_surjective₀ mul_right_surjective₀

lemma zero_zpow : ∀ n : ℤ, n ≠ 0 → (0 : G₀) ^ n = 0
  | (n : ℕ), h => by rw [zpow_natCast, zero_pow]; simpa [Int.natCast_eq_zero] using h
  | .negSucc n, _ => by simp
#align zero_zpow zero_zpow

lemma zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]
#align zero_zpow_eq zero_zpow_eq

lemma zpow_add_one₀ (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_natCast, pow_succ]
  | .negSucc 0 => by erw [zpow_zero, zpow_negSucc, pow_one, inv_mul_cancel ha]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq, zpow_neg, Int.neg_add, Int.neg_add_cancel_right, zpow_neg, ← Int.ofNat_succ,
      zpow_natCast, zpow_natCast, pow_succ' _ (n + 1), mul_inv_rev, mul_assoc, inv_mul_cancel ha,
      mul_one]
#align zpow_add_one₀ zpow_add_one₀

lemma zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]
#align zpow_sub_one₀ zpow_sub_one₀

lemma zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  · simp
  · simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  · rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]
#align zpow_add₀ zpow_add₀

lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or_iff, eq_self_iff_true, not_true, Ne, hm, hn, false_and_iff,
      or_false_iff] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
  · exact zpow_add₀ ha m n
#align zpow_add' zpow_add'

lemma zpow_one_add₀ (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add₀ h, zpow_one]
#align zpow_one_add₀ zpow_one_add₀

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]
#align div_mul_eq_mul_div₀ div_mul_eq_mul_div₀

lemma div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]
#align div_sq_cancel div_sq_cancel

end CommGroupWithZero
