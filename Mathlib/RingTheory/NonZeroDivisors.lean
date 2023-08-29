/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.GroupTheory.Submonoid.Membership

#align_import ring_theory.non_zero_divisors from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Non-zero divisors

In this file we define the submonoid `nonZeroDivisors` of a `MonoidWithZero`.

## Notations

This file declares the notation `R⁰` for the submonoid of non-zero-divisors of `R`,
in the locale `nonZeroDivisors`.

Use the statement `open nonZeroDivisors` to access this notation in your own code.

-/


section nonZeroDivisors

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `R`. -/
def nonZeroDivisors (R : Type*) [MonoidWithZero R] : Submonoid R where
  carrier := { x | ∀ z, z * x = 0 → z = 0 }
  one_mem' _ hz := by rwa [mul_one] at hz
                      -- 🎉 no goals
  mul_mem' hx₁ hx₂ _ hz := by
    -- ⊢ x✝ = 0
    rw [← mul_assoc] at hz
    -- 🎉 no goals
    exact hx₁ _ (hx₂ _ hz)
#align non_zero_divisors nonZeroDivisors

/-- The notation for the submonoid of non-zerodivisors. -/
scoped[nonZeroDivisors] notation:9000 R "⁰" => nonZeroDivisors R

open nonZeroDivisors

variable {M M' M₁ R R' F : Type*} [MonoidWithZero M] [MonoidWithZero M'] [CommMonoidWithZero M₁]
  [Ring R] [CommRing R']

theorem mem_nonZeroDivisors_iff {r : M} : r ∈ M⁰ ↔ ∀ x, x * r = 0 → x = 0 := Iff.rfl
#align mem_non_zero_divisors_iff mem_nonZeroDivisors_iff

theorem mul_right_mem_nonZeroDivisors_eq_zero_iff {x r : M} (hr : r ∈ M⁰) : x * r = 0 ↔ x = 0 :=
  ⟨hr _, by simp (config := { contextual := true })⟩
            -- 🎉 no goals
#align mul_right_mem_non_zero_divisors_eq_zero_iff mul_right_mem_nonZeroDivisors_eq_zero_iff
@[simp]
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {x : M} {c : M⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop
#align mul_right_coe_non_zero_divisors_eq_zero_iff mul_right_coe_nonZeroDivisors_eq_zero_iff

theorem mul_left_mem_nonZeroDivisors_eq_zero_iff {r x : M₁} (hr : r ∈ M₁⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]
  -- 🎉 no goals
#align mul_left_mem_non_zero_divisors_eq_zero_iff mul_left_mem_nonZeroDivisors_eq_zero_iff

@[simp]
theorem mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₁⁰} {x : M₁} : (c : M₁) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop
#align mul_left_coe_non_zero_divisors_eq_zero_iff mul_left_coe_nonZeroDivisors_eq_zero_iff

theorem mul_cancel_right_mem_nonZeroDivisors {x y r : R} (hr : r ∈ R⁰) : x * r = y * r ↔ x = y := by
  refine ⟨fun h ↦ ?_, congrArg (· * r)⟩
  -- ⊢ x = y
  rw [← sub_eq_zero, ← mul_right_mem_nonZeroDivisors_eq_zero_iff hr, sub_mul, h, sub_self]
  -- 🎉 no goals
#align mul_cancel_right_mem_non_zero_divisor mul_cancel_right_mem_nonZeroDivisors

theorem mul_cancel_right_coe_nonZeroDivisors {x y : R} {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop
#align mul_cancel_right_coe_non_zero_divisor mul_cancel_right_coe_nonZeroDivisors

@[simp]
theorem mul_cancel_left_mem_nonZeroDivisors {x y r : R'} (hr : r ∈ R'⁰) : r * x = r * y ↔ x = y :=
  by simp_rw [mul_comm r, mul_cancel_right_mem_nonZeroDivisors hr]
     -- 🎉 no goals
#align mul_cancel_left_mem_non_zero_divisor mul_cancel_left_mem_nonZeroDivisors

theorem mul_cancel_left_coe_nonZeroDivisors {x y : R'} {c : R'⁰} : (c : R') * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop
#align mul_cancel_left_coe_non_zero_divisor mul_cancel_left_coe_nonZeroDivisors

theorem nonZeroDivisors.ne_zero [Nontrivial M] {x} (hx : x ∈ M⁰) : x ≠ 0 := fun h ↦
  one_ne_zero (hx _ <| (one_mul _).trans h)
#align non_zero_divisors.ne_zero nonZeroDivisors.ne_zero

theorem nonZeroDivisors.coe_ne_zero [Nontrivial M] (x : M⁰) : (x : M) ≠ 0 :=
  nonZeroDivisors.ne_zero x.2
#align non_zero_divisors.coe_ne_zero nonZeroDivisors.coe_ne_zero

theorem mul_mem_nonZeroDivisors {a b : M₁} : a * b ∈ M₁⁰ ↔ a ∈ M₁⁰ ∧ b ∈ M₁⁰ := by
  constructor
  -- ⊢ a * b ∈ M₁⁰ → a ∈ M₁⁰ ∧ b ∈ M₁⁰
  · intro h
    -- ⊢ a ∈ M₁⁰ ∧ b ∈ M₁⁰
    constructor <;> intro x h' <;> apply h
    -- ⊢ a ∈ M₁⁰
                    -- ⊢ x = 0
                    -- ⊢ x = 0
                                   -- ⊢ x * (a * b) = 0
                                   -- ⊢ x * (a * b) = 0
    · rw [← mul_assoc, h', zero_mul]
      -- 🎉 no goals
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
      -- 🎉 no goals
  · rintro ⟨ha, hb⟩ x hx
    -- ⊢ x = 0
    apply ha
    -- ⊢ x * a = 0
    apply hb
    -- ⊢ x * a * b = 0
    rw [mul_assoc, hx]
    -- 🎉 no goals
#align mul_mem_non_zero_divisors mul_mem_nonZeroDivisors

theorem isUnit_of_mem_nonZeroDivisors {G₀ : Type*} [GroupWithZero G₀] {x : G₀}
    (hx : x ∈ nonZeroDivisors G₀) : IsUnit x :=
  ⟨⟨x, x⁻¹, mul_inv_cancel (nonZeroDivisors.ne_zero hx),
    inv_mul_cancel (nonZeroDivisors.ne_zero hx)⟩, rfl⟩
#align is_unit_of_mem_non_zero_divisors isUnit_of_mem_nonZeroDivisors

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0)
    (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx
#align eq_zero_of_ne_zero_of_mul_right_eq_zero eq_zero_of_ne_zero_of_mul_right_eq_zero

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0)
    (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx
#align eq_zero_of_ne_zero_of_mul_left_eq_zero eq_zero_of_ne_zero_of_mul_left_eq_zero

theorem mem_nonZeroDivisors_of_ne_zero [NoZeroDivisors M] {x : M} (hx : x ≠ 0) : x ∈ M⁰ := fun _ ↦
  eq_zero_of_ne_zero_of_mul_right_eq_zero hx
#align mem_non_zero_divisors_of_ne_zero mem_nonZeroDivisors_of_ne_zero

theorem mem_nonZeroDivisors_iff_ne_zero [NoZeroDivisors M] [Nontrivial M] {x : M} :
    x ∈ M⁰ ↔ x ≠ 0 := ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩
#align mem_non_zero_divisors_iff_ne_zero mem_nonZeroDivisors_iff_ne_zero

theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective (g : M → M')) {x : M} (h : x ∈ M⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))
#align map_ne_zero_of_mem_non_zero_divisors map_ne_zero_of_mem_nonZeroDivisors

theorem map_mem_nonZeroDivisors [Nontrivial M] [NoZeroDivisors M'] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective g) {x : M} (h : x ∈ M⁰) : g x ∈ M'⁰ := fun _ hz ↦
  eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h) hz
#align map_mem_non_zero_divisors map_mem_nonZeroDivisors

theorem le_nonZeroDivisors_of_noZeroDivisors [NoZeroDivisors M] {S : Submonoid M}
    (hS : (0 : M) ∉ S) : S ≤ M⁰ := fun _ hx _ hy ↦
  Or.recOn (eq_zero_or_eq_zero_of_mul_eq_zero hy) (fun h ↦ h) fun h ↦
    absurd (h ▸ hx : (0 : M) ∈ S) hS
#align le_non_zero_divisors_of_no_zero_divisors le_nonZeroDivisors_of_noZeroDivisors

theorem powers_le_nonZeroDivisors_of_noZeroDivisors [NoZeroDivisors M] {a : M} (ha : a ≠ 0) :
    Submonoid.powers a ≤ M⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ absurd (h.recOn fun _ hn ↦ pow_eq_zero hn) ha
#align powers_le_non_zero_divisors_of_no_zero_divisors powers_le_nonZeroDivisors_of_noZeroDivisors

theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M'] [MonoidWithZeroHomClass F M M']
    (f : F) (hf : Function.Injective f) {S : Submonoid M} (hS : S ≤ M⁰) : S.map f ≤ M'⁰ := by
  cases subsingleton_or_nontrivial M
  -- ⊢ Submonoid.map f S ≤ M'⁰
  · simp [Subsingleton.elim S ⊥]
    -- 🎉 no goals
  · exact le_nonZeroDivisors_of_noZeroDivisors fun h ↦
      let ⟨x, hx, hx0⟩ := h
      zero_ne_one (hS (hf (hx0.trans (map_zero f).symm) ▸ hx : 0 ∈ S) 1 (mul_zero 1)).symm
#align map_le_non_zero_divisors_of_injective map_le_nonZeroDivisors_of_injective

theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M']
    [MonoidWithZeroHomClass F M M'] (f : F) (hf : Function.Injective f) : M⁰ ≤ M'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)
#align non_zero_divisors_le_comap_non_zero_divisors_of_injective nonZeroDivisors_le_comap_nonZeroDivisors_of_injective

theorem prod_zero_iff_exists_zero [NoZeroDivisors M₁] [Nontrivial M₁] {s : Multiset M₁} :
    s.prod = 0 ↔ ∃ (r : M₁) (_ : r ∈ s), r = 0 := by
  constructor; swap
  -- ⊢ Multiset.prod s = 0 → ∃ r x, r = 0
               -- ⊢ (∃ r x, r = 0) → Multiset.prod s = 0
  · rintro ⟨r, hrs, rfl⟩
    -- ⊢ Multiset.prod s = 0
    exact Multiset.prod_eq_zero hrs
    -- 🎉 no goals
  induction' s using Multiset.induction_on with a s ih
  -- ⊢ Multiset.prod 0 = 0 → ∃ r x, r = 0
  · intro habs
    -- ⊢ ∃ r x, r = 0
    simp at habs
    -- 🎉 no goals
  · rw [Multiset.prod_cons]
    -- ⊢ a * Multiset.prod s = 0 → ∃ r x, r = 0
    intro hprod
    -- ⊢ ∃ r x, r = 0
    replace hprod := eq_zero_or_eq_zero_of_mul_eq_zero hprod
    -- ⊢ ∃ r x, r = 0
    cases' hprod with ha hb
    -- ⊢ ∃ r x, r = 0
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
      -- 🎉 no goals
    · apply (ih hb).imp _
      -- ⊢ ∀ (a_1 : M₁), (∃ x, a_1 = 0) → ∃ x, a_1 = 0
      rintro b ⟨hb₁, hb₂⟩
      -- ⊢ ∃ x, b = 0
      exact ⟨Multiset.mem_cons_of_mem hb₁, hb₂⟩
      -- 🎉 no goals
#align prod_zero_iff_exists_zero prod_zero_iff_exists_zero

end nonZeroDivisors
