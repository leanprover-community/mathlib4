/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.GroupTheory.Submonoid.Basic

/-!
# Zero divisors

## Main definitions

 * `nonZeroDivisorsLeft`: the elements of a `MonoidWithZero` that are not left zero divisors.
 * `nonZeroDivisorsRight`: the elements of a `MonoidWithZero` that are not right zero divisors.

-/

section MonoidWithZero

variable (M₀ : Type _) [MonoidWithZero M₀]

/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by simp
                 -- 🎉 no goals
  mul_mem' {x} {y} hx hy := fun z hz ↦ hx _ <| hy _ (mul_assoc z x y ▸ hz)

@[simp] lemma mem_nonZeroDivisorsLeft_iff {x : M₀} :
    x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, y * x = 0 → y = 0 :=
  Iff.rfl

/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by simp
                 -- 🎉 no goals
  mul_mem' := fun {x} {y} hx hy z hz ↦ hy _ (hx _ ((mul_assoc x y z).symm ▸ hz))

@[simp] lemma mem_nonZeroDivisorsRight_iff {x : M₀} :
    x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, x * y = 0 → y = 0 :=
  Iff.rfl

lemma nonZeroDivisorsLeft_eq_right (M₀ : Type _) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]
  -- ⊢ x ∈ nonZeroDivisorsLeft M₀ ↔ x ∈ nonZeroDivisorsRight M₀
         -- 🎉 no goals

@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  -- ⊢ x ∈ ↑(nonZeroDivisorsLeft M₀) ↔ x ∈ {x | x ≠ 0}
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_setOf_eq]
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by contradiction⟩
  -- ⊢ x ≠ 0
  contrapose! h
  -- ⊢ ∃ a, x = 0 ∧ a ≠ 0
  exact ⟨1, h, one_ne_zero⟩
  -- 🎉 no goals

@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  -- ⊢ x ∈ ↑(nonZeroDivisorsRight M₀) ↔ x ∈ {x | x ≠ 0}
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, Set.mem_setOf_eq]
  -- ⊢ (∀ (y : M₀), x = 0 ∨ y = 0 → y = 0) ↔ x ≠ 0
  refine' ⟨fun h ↦ _, fun hx y hx' ↦ by aesop⟩
  -- ⊢ x ≠ 0
  contrapose! h
  -- ⊢ ∃ y, (x = 0 ∨ y = 0) ∧ y ≠ 0
  exact ⟨1, Or.inl h, one_ne_zero⟩
  -- 🎉 no goals

end MonoidWithZero
