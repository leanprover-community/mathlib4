/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.OrderSynonym

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


open Classical

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
                        -- 🎉 no goals
                                                  -- 🎉 no goals
#align mul_eq_zero_of_ne_zero_imp_eq_zero mul_eq_zero_of_ne_zero_imp_eq_zero

/-- To match `one_mul_eq_id`. -/
theorem zero_mul_eq_const : (· * ·) (0 : M₀) = Function.const _ 0 :=
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
  -- 🎉 no goals
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

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_noZeroDivisors : NoZeroDivisors M₀ :=
  ⟨fun ab0 => or_iff_not_imp_left.mpr <| fun ha => mul_left_cancel₀ ha <|
    ab0.trans (mul_zero _).symm⟩
#align cancel_monoid_with_zero.to_no_zero_divisors CancelMonoidWithZero.to_noZeroDivisors

theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff
#align mul_left_inj' mul_left_inj'

theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff
#align mul_right_inj' mul_right_inj'

@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp [hc]; simp [mul_left_inj', hc]]
  -- 🎉 no goals
#align mul_eq_mul_right_iff mul_eq_mul_right_iff

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp [ha]; simp [mul_right_inj', ha]]
  -- 🎉 no goals
#align mul_eq_mul_left_iff mul_eq_mul_left_iff

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
                                    -- 🎉 no goals
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
#align mul_right_eq_self₀ mul_right_eq_self₀


theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
                                    -- 🎉 no goals
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
#align mul_left_eq_self₀ mul_left_eq_self₀

@[simp]
theorem mul_eq_left₀ (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]
  -- 🎉 no goals
#align mul_eq_left₀ mul_eq_left₀

@[simp]
theorem mul_eq_right₀ (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]
  -- 🎉 no goals
#align mul_eq_right₀ mul_eq_right₀

@[simp]
theorem left_eq_mul₀ (ha : a ≠ 0) : a = a * b ↔ b = 1 := by rw [eq_comm, mul_eq_left₀ ha]
                                                            -- 🎉 no goals
#align left_eq_mul₀ left_eq_mul₀

@[simp]
theorem right_eq_mul₀ (hb : b ≠ 0) : b = a * b ↔ a = 1 := by rw [eq_comm, mul_eq_right₀ hb]
                                                             -- 🎉 no goals
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

@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]
                -- 🎉 no goals
#align mul_inv_cancel_right₀ mul_inv_cancel_right₀


@[simp]
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
                -- 🎉 no goals
#align mul_inv_cancel_left₀ mul_inv_cancel_left₀


-- Porting note: used `simpa` to prove `False` in lean3
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  have := mul_inv_cancel h
  -- ⊢ False
  simp [a_eq_0] at this
  -- 🎉 no goals
#align inv_ne_zero inv_ne_zero

@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
                                          -- 🎉 no goals
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
                          -- 🎉 no goals
    _ = 1 := by simp [inv_ne_zero h]
                -- 🎉 no goals
#align inv_mul_cancel inv_mul_cancel


theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (fun y => x⁻¹ * y) w
  -- 🎉 no goals
#align group_with_zero.mul_left_injective GroupWithZero.mul_left_injective

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel _ h, mul_one] using congr_arg (fun y => y * x⁻¹) w
  -- 🎉 no goals
#align group_with_zero.mul_right_injective GroupWithZero.mul_right_injective

@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]
                -- 🎉 no goals
#align inv_mul_cancel_right₀ inv_mul_cancel_right₀


@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
                -- 🎉 no goals
#align inv_mul_cancel_left₀ inv_mul_cancel_left₀


private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]
  -- 🎉 no goals

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZero G₀› with
    inv := Inv.inv,
    inv_inv := fun a => by
      by_cases h : a = 0
      -- ⊢ a⁻¹⁻¹ = a
      · simp [h]
        -- 🎉 no goals

      · exact left_inv_eq_right_inv (inv_mul_cancel <| inv_ne_zero h) (inv_mul_cancel h)
        -- 🎉 no goals
        ,
    mul_inv_rev := fun a b => by
      by_cases ha : a = 0
      -- ⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹
      · simp [ha]
        -- 🎉 no goals

      by_cases hb : b = 0
      -- ⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹
      · simp [hb]
        -- 🎉 no goals

      refine' inv_eq_of_mul _
      -- ⊢ a * b * (b⁻¹ * a⁻¹) = 1
      simp [mul_assoc, ha, hb],
      -- 🎉 no goals
    inv_eq_of_mul := fun a b => inv_eq_of_mul }
#align group_with_zero.to_division_monoid GroupWithZero.toDivisionMonoid

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.toCancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZero G₀) with
    mul_left_cancel_of_ne_zero := @fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
      -- 🎉 no goals
    mul_right_cancel_of_ne_zero := @fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }
      -- 🎉 no goals
#align group_with_zero.to_cancel_monoid_with_zero GroupWithZero.toCancelMonoidWithZero

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]
                                            -- 🎉 no goals
#align zero_div zero_div

@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]
                                            -- 🎉 no goals
#align div_zero div_zero

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  -- ⊢ a * a * a⁻¹ = a
  · rw [h, inv_zero, mul_zero]
    -- 🎉 no goals
  · rw [mul_assoc, mul_inv_cancel h, mul_one]
    -- 🎉 no goals
#align mul_self_mul_inv mul_self_mul_inv


/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  -- ⊢ a * a⁻¹ * a = a
  · rw [h, inv_zero, mul_zero]
    -- 🎉 no goals
  · rw [mul_inv_cancel h, one_mul]
    -- 🎉 no goals
#align mul_inv_mul_self mul_inv_mul_self


/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  -- ⊢ a⁻¹ * a * a = a
  · rw [h, inv_zero, mul_zero]
    -- 🎉 no goals
  · rw [inv_mul_cancel h, one_mul]
    -- 🎉 no goals
#align inv_mul_mul_self inv_mul_mul_self


/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]
                                                         -- 🎉 no goals
#align mul_self_div_self mul_self_div_self

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_self a]
                                                         -- 🎉 no goals
#align div_self_mul_self div_self_mul_self

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
                                          -- 🎉 no goals
    _ = a⁻¹ := inv_mul_mul_self _
#align div_self_mul_self' div_self_mul_self'


theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h
  -- 🎉 no goals
#align one_div_ne_zero one_div_ne_zero

@[simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_eq_inv, inv_zero]
                                                     -- 🎉 no goals
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
  -- ⊢ a * a / a = a
  exact mul_self_div_self a
  -- 🎉 no goals
#align div_div_self div_div_self

theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align ne_zero_of_one_div_ne_zero ne_zero_of_one_div_ne_zero

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim
#align eq_zero_of_one_div_eq_zero eq_zero_of_one_div_eq_zero

theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel h]⟩
               -- 🎉 no goals
#align mul_left_surjective₀ mul_left_surjective₀

theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel h]⟩
               -- 🎉 no goals
#align mul_right_surjective₀ mul_right_surjective₀

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]
  -- 🎉 no goals
#align div_mul_eq_mul_div₀ div_mul_eq_mul_div₀

end CommGroupWithZero

/-! ### Order dual -/


open OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ := h

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ := h

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ := h

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ := h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero αᵒᵈ := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ := h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ := h

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ := h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ := h

/-! ### Lexicographic order -/


instance [h : MulZeroClass α] : MulZeroClass (Lex α) := h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) := h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) := h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) := h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero (Lex α) := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) := h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero (Lex α) := h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) := h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) := h
