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

In this file, we define lexicographical ordered `Lex (HahnSeries Γ R)`, and show this
is a `LinearOrder` when `Γ` and `R` themselves are linearly ordered. Additionally,
it is an ordered group when `R` is.

-/

namespace HahnSeries

variable {Γ R : Type*} [LinearOrder Γ]

section PartialOrder
variable [Zero R] [PartialOrder R]

instance : PartialOrder (Lex (HahnSeries Γ R)) :=
  PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y ↦ by simp

theorem lt_iff (a b : Lex (HahnSeries Γ R)) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → (ofLex a).coeff j = (ofLex b).coeff j)
    ∧ (ofLex a).coeff i < (ofLex b).coeff i := by rfl

end PartialOrder

section LinearOrder
variable [Zero R] [LinearOrder R]

noncomputable
instance : LinearOrder (Lex (HahnSeries Γ R)) where
  le_total a b := by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
    · have hab := Function.ne_iff.mp <| HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i ≠ 0} ∪ {i : Γ | (ofLex b).coeff i ≠ 0}
      let v := {i : Γ | (ofLex a).coeff i ≠ (ofLex b).coeff i}
      have hvu : v ⊆ u := by
        intro i h
        rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        contrapose! h
        rw [Set.notMem_setOf_iff, Mathlib.Tactic.PushNeg.not_ne_eq, h.1, h.2]
      have hv : v.IsWF :=
        ((ofLex a).isPWO_support'.isWF.union (ofLex b).isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i → (ofLex a).coeff j = (ofLex b).coeff j :=
        not_imp_not.mp <| fun h' ↦ hv.not_lt_min hab h'
      have hne : (ofLex a).coeff i ≠ (ofLex b).coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj ↦ (hji j hj).symm, hi⟩)
  toDecidableLE := Classical.decRel _

theorem leadingCoeff_pos_iff {x : Lex (HahnSeries Γ R)} : 0 < (ofLex x).leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) ≠ 0 := leadingCoeff_ne_iff.mp hpos.ne.symm
    have htop : (ofLex x).orderTop ≠ ⊤ := ne_zero_iff_orderTop.mp hne
    use (ofLex x).orderTop.untop htop
    constructor
    · intro j hj
      simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
    · rw [coeff_untop_eq_leadingCoeff hne]
      simpa using hpos
  · intro ⟨i, hj, hi⟩
    have horder : (ofLex x).orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : (ofLex x).orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : ofLex x ≠ 0 := ne_zero_iff_orderTop.mpr htop
    have horder' : (ofLex x).orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [← coeff_untop_eq_leadingCoeff hne, horder']
    simpa using hi

theorem leadingCoeff_nonneg_iff {x : Lex (HahnSeries Γ R)} :
    0 ≤ (ofLex x).leadingCoeff ↔ 0 ≤ x := by
  constructor
  · intro h
    obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_iff.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · intro h
    obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

theorem leadingCoeff_neg_iff {x : Lex (HahnSeries Γ R)} : (ofLex x).leadingCoeff < 0 ↔ x < 0 := by
  simpa using (leadingCoeff_nonneg_iff (x := x)).not

theorem leadingCoeff_nonpos_iff {x : Lex (HahnSeries Γ R)} :
    (ofLex x).leadingCoeff ≤ 0 ↔ x ≤ 0 := by
  simpa using (leadingCoeff_pos_iff (x := x)).not

end LinearOrder

section OrderedMonoid
variable [PartialOrder R] [AddCommMonoid R] [AddLeftStrictMono R] [IsOrderedAddMonoid R]

instance : IsOrderedAddMonoid (Lex (HahnSeries Γ R)) where
  add_le_add_left a b hab c := by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, ?_, ?_⟩
      · intro j hji
        simpa using congrArg ((ofLex c).coeff j + ·) (hj j hji)
      · simpa using add_lt_add_left hi ((ofLex c).coeff i)

end OrderedMonoid

section OrderedGroup
variable [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

theorem support_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).support = (ofLex x).support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

theorem orderTop_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).orderTop = (ofLex x).orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

theorem order_abs [Zero Γ] (x : Lex (HahnSeries Γ R)) : (ofLex |x|).order = (ofLex x).order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x ≠ 0 := hne
    have habs : ofLex |x| ≠ 0 := by
      change |x| ≠ 0
      simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne habs, order_eq_orderTop_of_ne hne']
    apply orderTop_abs

theorem leadingCoeff_abs (x : Lex (HahnSeries Γ R)) :
    (ofLex |x|).leadingCoeff = |(ofLex x).leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le, ofLex_neg, leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]

end OrderedGroup

end HahnSeries
