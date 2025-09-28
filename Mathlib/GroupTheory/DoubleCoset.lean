/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Basic

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `setoid`: The double coset relation defined by two subgroups `H K` of `G`.
* `DoubleCoset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite
open scoped Pointwise

namespace DoubleCoset

/-- The double coset as an element of `Set α` corresponding to `s a t` -/
def doubleCoset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

@[deprecated (since := "2025-07-12")] alias _root_.Doset.doset := doubleCoset

lemma doubleCoset_eq_image2 (a : α) (s t : Set α) :
    doubleCoset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

@[deprecated (since := "2025-07-12")] alias _root_.Doset.doset_eq_image2 := doubleCoset_eq_image2

theorem mem_doubleCoset {s t : Set α} {a b : α} :
    b ∈ doubleCoset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y := by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

@[deprecated (since := "2025-07-12")] alias _root_.Doset.mem_doset := mem_doubleCoset

theorem mem_doubleCoset_self (H K : Subgroup G) (a : G) : a ∈ doubleCoset a H K :=
  mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

@[deprecated (since := "2025-07-12")] alias _root_.Doset.mem_doset_self := mem_doubleCoset_self

theorem doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset, doubleCoset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
    mul_assoc, mul_assoc, Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hh]

@[deprecated (since := "2025-07-12")] alias _root_.Doset.doset_eq_of_mem := doubleCoset_eq_of_mem

theorem mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : b ∈ doubleCoset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.mem_doset_of_not_disjoint := mem_doubleCoset_of_not_disjoint

theorem eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K := by
  rw [disjoint_comm] at h
  have ha : a ∈ doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.eq_of_not_disjoint := eq_of_not_disjoint

/-- The setoid defined by the double_coset relation -/
def setoid (H K : Set G) : Setoid G :=
  Setoid.ker fun x => doubleCoset x H K

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.setoid := setoid

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def Quotient (H K : Set G) : Type _ :=
  _root_.Quotient (setoid H K)

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.Quotient := Quotient

theorem rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.rel_iff := rel_iff

theorem bot_rel_eq_leftRel (H : Subgroup G) :
    ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b ∈ H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.bot_rel_eq_leftRel := bot_rel_eq_leftRel

theorem rel_bot_eq_right_group_rel (H : Subgroup G) :
    ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ ∈ H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.rel_bot_eq_right_group_rel := rel_bot_eq_right_group_rel

/-- Create a double coset out of an element of `H \ G / K` -/
def quotToDoubleCoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G :=
  doubleCoset q.out H K

@[deprecated (since := "2025-07-12")] alias _root_.Doset.quotToDoset := quotToDoubleCoset

/-- Map from `G` to `H \ G / K` -/
abbrev mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  Quotient.mk'' a

@[deprecated (since := "2025-07-12")] alias _root_.Doset.mk := mk

instance (H K : Subgroup G) : Inhabited (Quotient (H : Set G) K) :=
  ⟨mk H K (1 : G)⟩

theorem eq (H K : Subgroup G) (a b : G) :
    mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k := by
  rw [Quotient.eq'']
  apply rel_iff

@[deprecated (since := "2025-07-12")] alias _root_.Doset.eq := eq

theorem out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q :=
  Quotient.out_eq' q

@[deprecated (since := "2025-07-12")] alias _root_.Doset.out_eq' := out_eq'

theorem mk_out_eq_mul (H K : Subgroup G) (g : G) :
    ∃ h k : G, h ∈ H ∧ k ∈ K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k := by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc, ← T]

@[deprecated (since := "2025-07-12")] alias _root_.Doset.mk_out_eq_mul := mk_out_eq_mul

theorem mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G}
    (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H K b := by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.mk_eq_of_doset_eq := mk_eq_of_doubleCoset_eq

theorem disjoint_out {H K : Subgroup G} {a b : Quotient H K} :
    a ≠ b → Disjoint (doubleCoset a.out H K) (doubleCoset b.out (H : Set G) K) := by
  contrapose!
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)

@[deprecated (since := "2025-07-12")] alias _root_.Doset.disjoint_out := disjoint_out

theorem union_quotToDoubleCoset (H K : Subgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_inv_cancel_right]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.union_quotToDoset := union_quotToDoubleCoset

theorem doubleCoset_union_rightCoset (H K : Subgroup G) (a : G) :
    ⋃ k : K, op (a * k) • ↑H = doubleCoset a H K := by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hx, mul_inv_cancel_right]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.doset_union_rightCoset := doubleCoset_union_rightCoset

theorem doubleCoset_union_leftCoset (H K : Subgroup G) (a : G) :
    ⋃ h : H, (h * a : G) • ↑K = doubleCoset a H K := by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hy, one_mul, inv_mul_cancel, inv_mul_cancel_right]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.doset_union_leftCoset := doubleCoset_union_leftCoset

theorem left_bot_eq_left_quot (H : Subgroup G) :
    Quotient (⊥ : Subgroup G) (H : Set G) = (G ⧸ H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.left_bot_eq_left_quot := left_bot_eq_left_quot

theorem right_bot_eq_right_quot (H : Subgroup G) :
    Quotient (H : Set G) (⊥ : Subgroup G) = _root_.Quotient (QuotientGroup.rightRel H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

@[deprecated (since := "2025-07-12")]
alias _root_.Doset.right_bot_eq_right_quot := right_bot_eq_right_quot

end DoubleCoset
