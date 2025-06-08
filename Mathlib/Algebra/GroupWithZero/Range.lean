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

/-! # Range of MonoidHomWithZero
Given a function `f : A → B` whose codomain `B` is a `MonoidWithZero`, we define the
type `range₀`, by endowing the range of `f` with a `0` (inherited from that of `B`). We then
provide some properties of `range₀ f`. Hypotheses on `A`, `B` and `f` are added as needed: in
particular, when `B` is a `GroupWithZero` so is `range₀ f` and if `B` is commutative, then
`range₀ f` is also commutative and can be provided with a more explicit description (see
`MonoidHomWithZero.mem_range₀_iff_of_comm`).

## Main Results
* `range₀ f` is the smallest submonoid with zero containing the range of `f`;
* `range₀ f` is a `CancelCommMonoidWithZero` when its codomain is cancellative and non-trivial;
* `range₀ f` is a `GroupWithZero` when its codomain is a group with zero;
* When `A` is a monoid with zero and `f` is a homomorphism of monoids with zero, `range₀ f` can be
explicitely descibed as the elements that are ratios of terms in `range f` , see
`MonoidHomWithZero.mem_range₀_iff_of_comm`.

## Implementation details
The definition of `range₀` (as a `Submonoid B`) simply requires that `B` be a nontrivial
`CancelMonoidWithZero`, and no assumption neither on `A` nor on `f` is need. To define an instance
of `GroupWithZero` on `range₀ f`, we need `GroupWithZero B` but still no assumption on `A` or `f`.

Commutativity of `B` and compatiblity of `f` with the monoidal structures is only required to
provide the explicit description of `range₀ f` in `MonoidHomWithZero.mem_range₀_iff_of_comm`.

-/

namespace MonoidHomWithZero

open Set

variable {A B F : Type*} [FunLike F A B] (f : F)

section CancelMonoidWithZero

variable  [CancelMonoidWithZero B] [Nontrivial B]


/-- For a map with codomain a `MonoidWithZero`, this is a smallest
`MondoidWithZero` that contains the image. When the codomain is a `GroupWithZero`, so is
`range₀ f`. See also `range₀'` for an alternative definition with more assumptions on `B` and `f`,
and `blabla` for a proof that `range₀ f = range₀' f` under those assumptions. -/
def range₀ : Submonoid B where
  carrier := (↑)''(Subgroup.closure (G := Bˣ) ((↑)⁻¹' (range f))).carrier ∪ {0}
  mul_mem' {b b'} hb hb' := by
    simp only [union_singleton, mem_insert_iff, mul_eq_zero, mem_image, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid] at hb hb' ⊢
    rcases hb with hb | ⟨a, ha, rfl⟩ <;> rcases hb' with hb' | ⟨a', ha', rfl⟩
    rotate_right
    · exact Or.inr ⟨a * a', by simpa only [Units.val_mul, and_true] using Subgroup.mul_mem _ ha ha'⟩
    all_goals tauto
  one_mem' := by simpa using Subgroup.one_mem ..

theorem mem_range₀ {a : A} : f a ∈ range₀ f := by
  sorry

instance : CancelMonoidWithZero (range₀ f) where
  zero := ⟨0, by simp [range₀]⟩
  zero_mul a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact zero_mul ..
  mul_zero a := by
    rw [← Subtype.coe_inj, Submonoid.coe_mul]
    exact mul_zero ..
  mul_left_cancel_of_ne_zero := by
    rintro ⟨x, _⟩ ⟨_, _⟩ ⟨_, _⟩ ha H
    have : x ≠ 0 := Subtype.coe_ne_coe.mpr ha
    simpa [this] using H
  mul_right_cancel_of_ne_zero {a b c} ha H := by
    rcases b with ⟨x, _⟩; rcases a; rcases c
    have : x ≠ 0 := Subtype.coe_ne_coe.mpr ha
    simpa [this] using H

theorem zero_mem_range₀ : 0 ∈ range₀ f := by
  simp [range₀]

@[simp]
theorem range₀_coe_zero : ((0 : range₀ f) : B) = 0 := rfl

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero B]

@[simp]
theorem range₀_coe_one : ((1 : range₀ f) : B) = 1 := rfl

theorem inv_mem_range₀ {b : B} (hb : b ∈ range₀ f) : b⁻¹ ∈ range₀ f := by
  simp only [range₀, union_singleton, inv_zero, Submonoid.mem_mk, Subsemigroup.mem_mk,
    mem_insert_iff, mem_image, Units.ne_zero, and_false, exists_const, or_false] at hb ⊢
  rcases hb with hb | ⟨a, ha, rfl⟩
  · simp [hb]
  exact Or.inr ⟨a⁻¹, by simpa⟩

instance : GroupWithZero (range₀ f) where
  toMonoidWithZero := inferInstance
  inv a := by
    rcases a with ⟨a, ha⟩
    exact ⟨a⁻¹, inv_mem_range₀ _ ha⟩
  exists_pair_ne := by
    use 1, ⟨0, by simp [range₀]⟩
    simp [← Subtype.coe_inj]
  inv_zero := Subtype.coe_inj.symm.mpr inv_zero
  mul_inv_cancel a ha₀ := by
    rw [Submonoid.mk_mul_mk, Submonoid.mk_eq_one, mul_inv_cancel₀]
    rwa [← Subtype.coe_ne_coe] at ha₀

theorem inv_mem_range₀_iff {b : B} : b⁻¹ ∈ range₀ f ↔ b ∈ range₀ f := by
  by_cases h : b = 0
  · simp only [h, inv_zero, zero_mem_range₀]
  exact ⟨fun h ↦ ((inv_inv b).symm ▸ (inv_mem_range₀ f)) h, inv_mem_range₀ _⟩

end GroupWithZero

section CommGroupWithZero

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_range₀_iff_of_comm (y : B) :
    y ∈ range₀ f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f a * y = f x := by
  refine ⟨fun hy ↦ ?_, fun ⟨a, ha, ⟨x, hy⟩⟩ ↦ ?_⟩
  · simp [range₀] at hy
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
      exact mul_mul_mul_comm (f u) (f v) ↑c ↑d
    | inv c hc hcy  =>
      obtain ⟨u, hu, ⟨a, ha⟩⟩ := hcy _ (refl _)
      use a
      simp [← ha, hu]
      use u
      simp [← huy]
  · simp [range₀]
    rcases GroupWithZero.eq_zero_or_unit y with h | h
    · simp [h]
    · right
      obtain ⟨c, rfl⟩ := h
      use c
      simp
      set u := (Ne.isUnit ha).unit
      have hu : f a = u := by simp [u]
      have hv : IsUnit (f x) := by simp [← hy, hu]
      set v := hv.unit
      replace hv : f x = v := by simp [v]
      suffices c = v / u by
        rw [this]
        apply Subgroup.div_mem
        · apply Subgroup.subset_closure
          simp [← hv]
        · apply Subgroup.subset_closure
          simp [← hu]
      rw [eq_div_iff_mul_eq', mul_comm, ← Units.eq_iff,
        Units.val_mul, ← hu, ← hv, hy]

/-- `MonoidHomWithZero.range₀' f` is a `CommGroupWithZero`  when the codomain is commutative. -/
instance : CommGroupWithZero (range₀ f) where
  toGroupWithZero := inferInstance
  mul_comm := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [mem_range₀_iff_of_comm] at ha hb
    obtain ⟨x, hx, ⟨c, hc⟩⟩ := ha; obtain ⟨y, hy, ⟨d, hd⟩⟩ := hb
    simp
    rw [← eq_inv_mul_iff_mul_eq₀] at hc hd
    · rw [hc, hd, mul_comm]
    exacts [hy, hx]


end CommGroupWithZero

end MonoidHomWithZero
