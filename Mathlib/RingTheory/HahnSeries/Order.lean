/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.PiLex
import Mathlib.RingTheory.HahnSeries.Addition

/-!

# Lexicographical order on Hahn series

In this file, we equip `HahnSeries Γ R` with lexicographical order, and show this
is a `LinearOrder` when `Γ` and `R` themselves are linearly ordered. Additionally,
it is an ordered group when `R` is.

-/

namespace HahnSeries

section PartialOrder

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [Zero R] [PartialOrder R]

variable (Γ R) in
instance instPartialOrder : PartialOrder (HahnSeries Γ R) :=
  PartialOrder.lift (toLex ·.coeff) (by
    intro x y
    simp
  )

theorem lt_iff (a b : HahnSeries Γ R) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → a.coeff j = b.coeff j) ∧ a.coeff i < b.coeff i := by rfl

end PartialOrder

section LinearOrder

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [Zero R] [LinearOrder R]

variable (Γ R) in
noncomputable
instance instLinearOrder : LinearOrder (HahnSeries Γ R) where
  le_total := by
    intro a b
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
    · have hab := Function.ne_iff.mp <| HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | a.coeff i ≠ 0} ∪ {i : Γ | b.coeff i ≠ 0}
      let v := {i : Γ | a.coeff i ≠ b.coeff i}
      have hvu : v ⊆ u := by
        intro i h
        rw [Set.mem_union, Set.mem_setOf_eq, or_iff_not_imp_left]
        intro h2
        rw [not_ne_iff] at h2
        rw [Set.mem_setOf_eq, h2] at h
        exact h.symm
      have hv : v.IsWF := (a.isPWO_support'.isWF.union b.isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i → a.coeff j = b.coeff j :=
        not_imp_not.mp <| fun h' ↦ hv.not_lt_min hab h'
      have hne : a.coeff i ≠ b.coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj ↦ (hji j hj).symm, hi⟩)

  toDecidableLE := Classical.decRel _

theorem leadingCoeff_pos_iff {x : HahnSeries Γ R} : 0 < x.leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : x ≠ 0 := leadingCoeff_ne_iff.mp hpos.ne.symm
    have htop : x.orderTop ≠ ⊤ := ne_zero_iff_orderTop.mp hne
    use x.orderTop.untop htop
    constructor
    · intro j hj
      simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
    · rw [← leadingCoeff_eq_coeff_orderTop hne]
      simpa using hpos
  · intro ⟨i, hj, hi⟩
    have horder : x.orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : x.orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : x ≠ 0 := ne_zero_iff_orderTop.mpr htop
    have horder' : x.orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [leadingCoeff_eq_coeff_orderTop hne, horder']
    simpa using hi

theorem leadingCoeff_neg_iff {x : HahnSeries Γ R} : x.leadingCoeff < 0 ↔ x < 0 := by
  constructor
  · intro h
    contrapose! h
    obtain rfl | hlt := eq_or_lt_of_le h
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le
  · intro h
    contrapose! h
    obtain heq | hlt := eq_or_lt_of_le h
    · exact (leadingCoeff_eq_iff.mp heq.symm).symm.le
    · exact (leadingCoeff_pos_iff.mp hlt).le

theorem leadingCoeff_nonneg_iff {x : HahnSeries Γ R} : 0 ≤ x.leadingCoeff ↔ 0 ≤ x := by
  simpa using (leadingCoeff_neg_iff (x := x)).not

theorem leadingCoeff_nonpos_iff {x : HahnSeries Γ R} : x.leadingCoeff ≤ 0 ↔ x ≤ 0 := by
  simpa using (leadingCoeff_pos_iff (x := x)).not

end LinearOrder

section OrderedGroup

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

variable (Γ) in
instance instIsOrderedAddMonoid (R : Type*) [PartialOrder R] [AddCommGroup R]
    [IsOrderedAddMonoid R] : IsOrderedAddMonoid (HahnSeries Γ R) where
  add_le_add_left := by
    intro a b hab c
    obtain rfl | hlt := eq_or_lt_of_le hab
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hi⟩ := hlt
      use i
      aesop

theorem support_abs (x : HahnSeries Γ R) : |x|.support = x.support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

theorem orderTop_abs (x : HahnSeries Γ R) : |x|.orderTop = x.orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

theorem order_abs [Zero Γ] (x : HahnSeries Γ R) : |x|.order = x.order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne (by simpa using hne), order_eq_orderTop_of_ne hne]
    apply orderTop_abs

theorem leadingCoeff_abs (x : HahnSeries Γ R) : |x|.leadingCoeff = |x.leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le, leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]

end OrderedGroup

end HahnSeries
