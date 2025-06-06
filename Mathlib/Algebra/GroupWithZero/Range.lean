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

variable {A B C : Type*}
  -- [Monoid A]
  [GroupWithZero B]
  [CommGroupWithZero C]
--[CancelMonoidWithZero B] [Nontrivial B]
  {F : Type*} [FunLike F A B] (f : F)
  -- [MonoidHomClass F A B]
  {G : Type*} [FunLike G A C] (g : G)

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

-- variable [Monoid A] [MonoidHomClass F A B]

/-- The range of a morphism of monoids with codomain a `CommGroupWithZero`,
as a `CommGroupWithZero` -/
def range₀ [MonoidWithZero A] [MonoidWithZeroHomClass G A C] :
    Submonoid C where
  carrier := { b | ∃ a c, g a ≠ 0 ∧ (g a * b = g c)}
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

example [MonoidWithZero A] [MonoidWithZeroHomClass G A C] :
    frange₀ g = range₀ g := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · simp [range₀]
    simp [frange₀] at hy
    rcases hy with hy | ⟨u, hu, huy⟩
    · use 1
      simp [map_one, one_ne_zero]
      use 0
      rw [hy, map_zero]
    induction hu using Subgroup.closure_induction generalizing y with
    | mem c hc =>
      simp only [mem_preimage, mem_range] at hc
      obtain ⟨a, ha⟩ := hc
      use 1
      simp [← huy]
      use a, ha.symm
    | one =>
      simp [← huy]
      use 1
      simp
    | mul c d hc hd hcy hdy =>
      simp only [Units.val_mul] at huy
      obtain ⟨u, hu, ⟨a, ha⟩⟩ := hcy c (refl _)
      obtain ⟨v, hv, ⟨b, hb⟩⟩ := hdy d (refl _)
      use u * v
      simp [hu, hv]
      use a * b
      simp [← ha, ← hb, ← huy]
      exact mul_mul_mul_comm (g u) (g v) ↑c ↑d
    | inv c hc hcy  =>
      obtain ⟨u, hu, ⟨a, ha⟩⟩ := hcy _ (refl _)
      use a
      simp [← ha, hu]
      use u
      simp [← huy]
  · simp [range₀] at hy
    obtain ⟨a, ha, ⟨x, hy⟩⟩ := hy
    simp [frange₀]
    rcases GroupWithZero.eq_zero_or_unit y with h | h
    · simp [h]
    · right
      obtain ⟨c, rfl⟩ := h
      use c
      simp
      set u := (Ne.isUnit ha).unit
      have hu : g a = u := by simp [u]
      have hv : IsUnit (g x) := by simp [← hy, hu]
      set v := hv.unit
      replace hv : g x = v := by simp [v]
      suffices c = v / u by
        rw [this]
        apply Subgroup.div_mem
        · apply Subgroup.subset_closure
          simp [← hv]
        · apply Subgroup.subset_closure
          simp [← hu]
      rw [eq_div_iff_mul_eq', mul_comm, ← Units.eq_iff,
        Units.val_mul, ← hu, ← hv, hy]

/- Ce qui est au-dessus prouve l'égalité de `frange₀` et `range₀`
quand les deux sont définis.
À mon sens, il faudrait se contenter de la définition de `frange₀`
qu'on peut renommer `range₀`
et changer l'`example` ci-dessus en un
`mem_range₀_iff`  -/

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
