/-
Copyright (c) 2025 Antoine Chambert-Loir and Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Filippo Nuccio
-/

import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NthRewrite

variable {A B : Type*} [MonoidWithZero A] [CommGroupWithZero B]
  {F : Type*} [FunLike F A B] [MonoidHomClass F A B]
  (f : F)

namespace MonoidHomWithZero

open Set

/-- The range of a morphism of monoids with codomain a `CommGroupWithZero`,
as a `CommGroupWithZero` -/
def range₀ : Submonoid B where
  carrier := { b | ∃ a c, f a ≠ 0 ∧  (f a * b = f c)}
  mul_mem' {b b'} hb hb' := by
    simp only [ne_eq, mem_setOf_eq] at hb hb' ⊢
    obtain ⟨a, c, ha, h⟩ := hb
    obtain ⟨a', c', ha', h'⟩ := hb'
    refine ⟨a * a', c * c', by simp [ha, ha'], ?_⟩
    simp only [_root_.map_mul, ← h, ← h']
    simp only [mul_assoc]; apply congr_arg₂ _ rfl
    simp only [← mul_assoc]; apply congr_arg₂ _ _ rfl
    rw [mul_comm]
  one_mem' := by
    simp only [ne_eq, exists_and_left, mem_setOf_eq, mul_one, exists_apply_eq_apply', and_true]
    use 1
    rw [_root_.map_one]
    exact one_ne_zero

variable {f}

theorem range₀_coe_one : ((1 : range₀ f) : B) = 1 := rfl

theorem mem_range₀_iff {b : B} :
    b ∈ range₀ f ↔ ∃ a c, (f a ≠ 0 ∧ f a * b = f c) := by
  simp [range₀]

theorem mem_range₀ {a : A} : f a ∈ range₀ f := by
  rw [mem_range₀_iff]
  refine ⟨1, a, by simp⟩

variable [ZeroHomClass F A B]

theorem zero_mem_range₀ : 0 ∈ range₀ f := by
  rw [mem_range₀_iff]
  refine ⟨1, 0, ?_, by simp⟩
  rw [_root_.map_one]; exact one_ne_zero

theorem inv_mem_range₀ {b : B} (hb : b ∈ range₀ f) :
    b⁻¹ ∈ range₀ f := by
  by_cases h : b = 0
  · simp only [h, inv_zero, zero_mem_range₀]
  simp only [mem_range₀_iff] at hb ⊢
  obtain ⟨a, c, ha, hc⟩ := hb
  refine ⟨c, a, by simp [← hc, ha, h]⟩

theorem inv_mem_range₀_iff {b : B} :
    b⁻¹ ∈ range₀ f ↔ b ∈ range₀ f := by
  constructor
  · nth_rewrite 2 [← inv_inv b]
    exact inv_mem_range₀
  · exact inv_mem_range₀

/-- `MonoidHom.range₀ f` is a `CommGroupWithZero` -/
instance : CommGroupWithZero (range₀ f) where
  toCommMonoid := inferInstance
  zero := ⟨0, zero_mem_range₀⟩
  zero_mul a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact zero_mul _
  mul_zero a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact mul_zero _
  inv b := ⟨b⁻¹, inv_mem_range₀ b.prop⟩
  exists_pair_ne := by
    use 1, ⟨0, zero_mem_range₀⟩
    rw [ne_eq, ← Subtype.coe_inj]
    exact one_ne_zero
  inv_zero := by
    rw [← Subtype.coe_inj]
    exact inv_zero
  mul_inv_cancel b hb := by
    obtain ⟨a, c, ha, hc⟩ := mem_range₀_iff.mpr b.prop
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    apply mul_inv_cancel₀
    rwa [ne_eq, ← Subtype.coe_inj] at hb

theorem range₀_coe_zero : ((0 : range₀ f) : B) = 0 := rfl

end MonoidHomWithZero
