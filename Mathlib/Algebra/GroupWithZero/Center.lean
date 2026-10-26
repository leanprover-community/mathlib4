/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Center of a group with zero
-/

public section

assert_not_exists RelIso Finset Ring Subsemigroup

variable {M₀ G₀ : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s : Set M₀}

@[simp] lemma zero_mem_center : (0 : M₀) ∈ center M₀ where
  comm _ := by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]

@[simp] lemma zero_mem_centralizer : (0 : M₀) ∈ centralizer s := by simp [mem_centralizer_iff]

instance : MulZeroClass (Center M₀) where
  zero := Center.mk (0 : M₀) zero_mem_center
  zero_mul m := Subtype.ext (zero_mul m.val)
  mul_zero m := Subtype.ext (mul_zero m.val)

@[simp]
lemma _root_.Center.coe_zero :  (0 : Center M₀).val = 0 := rfl

end MulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

lemma center_units_subset : center G₀ˣ ⊆ ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
  · exact congr_arg Units.val <| hu <| Units.mk0 a ha

/-- In a group with zero, the center of the units is the preimage of the center. -/
lemma center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ :=
  center_units_subset.antisymm subset_center_units

@[simp] lemma inv_mem_centralizer₀ (ha : a ∈ centralizer s) : a⁻¹ ∈ centralizer s := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_centralizer
  · rintro c hc
    rw [mul_inv_eq_iff_eq_mul₀ ha₀, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha₀, ha c hc]

@[simp] lemma div_mem_centralizer₀ (ha : a ∈ centralizer s) (hb : b ∈ centralizer s) :
    a / b ∈ centralizer s := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer₀ hb)


instance : CommGroupWithZero (Center G₀) where
  exists_pair_ne := ⟨0, 1, by rw [ne_eq, Center.eq_iff]; exact zero_ne_one⟩
  inv_zero := by simp
  mul_inv_cancel := by simp_all

end GroupWithZero
end Set
