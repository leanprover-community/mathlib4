/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Centralizer
import Mathlib.Algebra.GroupWithZero.Units.Basic

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Center of a group with zero
-/

assert_not_exists Finset
assert_not_exists Ring
assert_not_exists Subsemigroup

variable {M₀ G₀ : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s : Set M₀}

variable (M₀) in
@[simp] theorem zero_mem_center : (0 : M₀) ∈ center M₀ where
  comm _ := by rw [zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  mid_assoc _ _ := by rw [mul_zero, zero_mul, mul_zero]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]
#align set.zero_mem_center Set.zero_mem_center

variable (s) in
@[simp] theorem zero_mem_centralizer : (0 : M₀) ∈ centralizer s := by simp [mem_centralizer_iff]
#align set.zero_mem_centralizer Set.zero_mem_centralizer

end MulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

theorem center_units_subset : Set.center G₀ˣ ⊆ ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ :=
  fun _ ha => by
    rw [mem_preimage, _root_.Semigroup.mem_center_iff]
    intro b
    obtain rfl | hb := eq_or_ne b 0
    · rw [zero_mul, mul_zero]
    · exact Units.ext_iff.mp (ha.comm (Units.mk0 b hb)).symm
#align set.center_units_subset Set.center_units_subset

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ :=
  Subset.antisymm center_units_subset subset_center_units
#align set.center_units_eq Set.center_units_eq

@[simp] theorem inv_mem_centralizer₀ (ha : a ∈ centralizer s) : a⁻¹ ∈ centralizer s :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer s)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]
#align set.inv_mem_centralizer₀ Set.inv_mem_centralizer₀

@[simp] theorem div_mem_centralizer₀ (ha : a ∈ centralizer s) (hb : b ∈ centralizer s) :
    a / b ∈ centralizer s := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)
#align set.div_mem_centralizer₀ Set.div_mem_centralizer₀

@[deprecated inv_mem_center (since := "2024-06-17")]
theorem inv_mem_center₀ (ha : a ∈ Set.center G₀) : a⁻¹ ∈ Set.center G₀ :=
  inv_mem_center ha
#align set.inv_mem_center₀ Set.inv_mem_centerₓ

@[deprecated div_mem_center (since := "2024-06-17")]
theorem div_mem_center₀ (ha : a ∈ Set.center G₀) (hb : b ∈ Set.center G₀) : a / b ∈ Set.center G₀ :=
  div_mem_center ha hb
#align set.div_mem_center₀ Set.div_mem_centerₓ

end GroupWithZero
end Set
