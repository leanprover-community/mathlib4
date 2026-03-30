/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.LocalExtr

/-!
# Local maxima from monotonicity and antitonicity

In this file we prove a lemma that is useful for the First Derivative Test in calculus,
and its dual.

## Main statements

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

* `isLocalMin_of_anti_mono` : the dual statement for minima.

-/

public section

open Set

variable {α β : Type*} [LinearOrder α] [Preorder β] {s : Set α} {a b c : α} {f : α → β}

/-- If `f` is monotone on `(a, b]` and antitone on `[b,c)`, then the maximum of `f` on `(a, c)` is
attained at `b`. -/
lemma isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ioo a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `(a, b]` and monotone on `[b,c)`, then the minimum of `f` on `(a, c)` is
attained at `b`. -/
lemma isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ioo a c) b :=
  isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `[a, b]` and antitone on `[b,c)`, then the maximum of `f` on `[a, c)` is
attained at `b`. -/
lemma isMaxOn_Ico_of_mono_anti
    (h₀ : MonotoneOn f (Icc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ico a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `[a, b]` and monotone on `[b,c)`, then the minimum of `f` on `[a, c)` is
attained at `b`. -/
lemma isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ico a c) b :=
  isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(a, b]` and antitone on `[b,c]`, then the maximum of `f` on `(a, c]` is
attained at `b`. -/
lemma isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Ioc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is monotone on `(a, b]` and antitone on `[b,c]`, then the maximum of `f` on `(a, c]` is
attained at `b`. -/
lemma isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Ioc a c) b :=
  isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `[a, b]` and antitone on `[b,c]`, then the maximum of `f` on `[a, c]` is
attained at `b`. -/
lemma isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Icc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `[a, b]` and monotone on `[b,c]`, then the minimum of `f` on `(a, c]` is
attained at `b`. -/
lemma isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Icc a c) b :=
  isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(a, b]` and antitone on `[b,∞)`, then the maximum of `f` on `(a, ∞)` is
attained at `b`. -/
lemma isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ioi a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `(a, b]` and monotone on `[b,∞)`, then the minimum of `f` on `(a, ∞)` is
attained at `b`. -/
lemma isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ioi a) b :=
  isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `[a, b]` and antitone on `[b,∞)`, then the maximum of `f` on `[a, ∞)` is
attained at `b`. -/
lemma isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ici a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `(a, b]` and monotone on `[b,∞)`, then the minimum of `f` on `[a, ∞)` is
attained at `b`. -/
lemma isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ici a) b :=
  isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(-∞, b]` and antitone on `[b,a)`, then the maximum of `f` on `(-∞, a)` is
attained at `b`. -/
lemma isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a)) :
    IsMaxOn f (Iio a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `(-∞, b]` and monotone on `[b,a)`, then the minimum of `f` on `(-∞, a)` is
attained at `b`. -/
lemma isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a)) :
    IsMinOn f (Iio a) b :=
  isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(-∞, b]` and antitone on `[b,a]`, then the maximum of
`f` on `(-∞, a]` is attained at `b`. -/
lemma isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a)) :
    IsMaxOn f (Iic a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `(-∞, b]` and monotone on `[b,a]`, then the minimum of `f` on `(-∞, a]` is
attained at `b`. -/
lemma isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a)) :
    IsMinOn f (Iic a) b :=
  isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(-∞, b]` and antitone on `[b,∞)`, then the maximum of `f` is attained
at `b`. -/
lemma isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f univ b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `f` is antitone on `(-∞, b]` and monotone on `[b,∞)`, then the minimum of `f` is attained
at `b`. -/
lemma isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f univ b :=
  isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  (isMaxOn_Ioo_of_mono_anti h₀ h₁).isLocalMax (Ioo_mem_nhds g₀ g₁)

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  isLocalMax_of_mono_anti (β := βᵒᵈ) g₀ g₁ h₀ h₁
