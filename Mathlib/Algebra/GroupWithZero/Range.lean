/-
Copyright (c) 2025 Antoine Chambert-Loir and Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Filippo A. E. Nuccio
-/

import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # The range of a `MonoidHom`,
  when the codomain is a `GroupWithZero`, turned into a `GroupWithZero`.

If `f : A →* B` is a multiplicative map, where `B` is a `CommGroupWithZero`,
then `f.range₀` is the smallest submonoid of `B`
containing the image of `f` which is a `CommGroupWithZero`.
-/

variable {A B : Type*} [MonoidWithZero A] [CommGroupWithZero B]--[CancelMonoidWithZero B] [Nontrivial B]
  {F : Type*} [FunLike F A B] [MonoidHomClass F A B]
  (f : F)

namespace MonoidHomWithZero

open Set

-- open Submonoid in
-- def frange₀ : Submonoid B where
--   carrier := closure (range f) ∪ {0}
--   mul_mem' {b b'} hb hb' := by
--     simp only [mem_union, SetLike.mem_coe, mem_singleton_iff] at hb hb' ⊢
--     rcases hb' with hb' | hb'; all_goals rcases hb with hb | hb';
--     · left
--       exact Submonoid.mul_mem _ hb hb'
--     all_goals
--       right
--       simp [hb', zero_mul, mul_zero]
--   one_mem' := by
--     simpa only [union_singleton, mem_insert_iff, one_ne_zero, SetLike.mem_coe, false_or] using
--       one_mem <| closure _

def frange₀ : Submonoid B where
  carrier := (↑)''(Subgroup.closure (G := Bˣ) ((↑)⁻¹' (range f))).carrier ∪ {0}
  mul_mem' {b b'} hb hb' := by
    simp only [union_singleton, mem_insert_iff, mul_eq_zero, mem_image, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid] at hb hb' ⊢
    rcases hb with hb | ⟨a, ha, rfl⟩ <;> rcases hb' with hb' | ⟨a', ha', rfl⟩
    rotate_right
    · right
      exact ⟨a * a', by simpa only [Units.val_mul, and_true] using Subgroup.mul_mem _ ha ha'⟩
    all_goals tauto
  one_mem' := by
    simpa only [union_singleton, mem_insert_iff, one_ne_zero, mem_image, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Units.val_eq_one, exists_eq_right,
      false_or] using Subgroup.one_mem ..

theorem inv_mem_frange₀ {b : B} (hb : b ∈ frange₀ f) :
    b⁻¹ ∈ frange₀ f := by
  simp only [frange₀, union_singleton, inv_zero, Submonoid.mem_mk, Subsemigroup.mem_mk,
    mem_insert_iff, mem_image, Units.ne_zero, and_false, exists_const, or_false] at hb ⊢
  rcases hb with hb | ⟨a, ha, rfl⟩
  · left
    rw [hb, inv_zero]
  right
  use a⁻¹
  simpa

instance : GroupWithZero (frange₀ f) where
  toMonoid := inferInstance
  zero := ⟨0, by simp [frange₀]⟩
  zero_mul a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact zero_mul ..
  mul_zero a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact mul_zero ..
  inv a := by
    rcases a with ⟨a, ha⟩
    exact ⟨a⁻¹, inv_mem_frange₀ _ ha⟩
  exists_pair_ne := by
    use 1, ⟨0, by simp [frange₀]⟩
    rw [ne_eq, ← Subtype.coe_inj]
    exact one_ne_zero
  inv_zero := by
    simp [← Subtype.coe_inj]
    exact inv_zero
  mul_inv_cancel a ha₀ := by
    rw [Submonoid.mk_mul_mk, Submonoid.mk_eq_one, mul_inv_cancel₀]
    rw [← Subtype.coe_ne_coe] at ha₀
    exact ha₀


/-- The range of a morphism of monoids with codomain a `CommGroupWithZero`,
as a `CommGroupWithZero` -/
def range₀ : Submonoid B where
  carrier := { b | ∃ a c, f a ≠ 0 ∧ (f a * b = f c)}
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


example [ZeroHomClass F A B] : frange₀ f = range₀ f := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · simp [range₀]
    simp [frange₀] at hy
    rcases hy with hy | ⟨u, hu, huy⟩
    · use 1
      rw [map_one]
      constructor
      · exact one_ne_zero
      use 0
      rw [hy]
      rw [mul_zero, map_zero]
    have := @Subgroup.closure_induction (G := Bˣ) (k := ((↑)⁻¹' (range f))) _
      (fun u hu ↦ ∃ a : A, ¬ f a = 0 ∧ ∃ x : A, f a * u = f x)
      (x := u)
    rw [huy] at this
    apply this
    · intro v hv_prop
      obtain ⟨y, hy⟩ := hv_prop
      rw [← hy]
      use 1
      constructor
      · rw [map_one]
        exact one_ne_zero
      use y
      rw [map_one, one_mul]
    · use 1
      rw [map_one]
      constructor
      · exact one_ne_zero
      use 1
      simp
    · rintro a b ha hb ⟨t, ht₀, ⟨s, hs⟩⟩ ⟨t', ht'₀, ⟨s', hs'⟩⟩
      use t * t'
      constructor
      · sorry
      use s * s'
      rw [map_mul, Units.val_mul, map_mul, ← hs, ← hs']
      rw [mul_assoc (f t), mul_comm (f t'), mul_comm (f t'), mul_assoc (a : B),
         mul_assoc _ (a : B)]
    · sorry
    · exact hu
  sorry

variable {f}

@[simp]
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

@[simp]
theorem range₀_coe_zero : ((0 : range₀ f) : B) = 0 := rfl

end MonoidHomWithZero
