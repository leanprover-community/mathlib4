/-
Copyright (c) 2024 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Sums in `WithTop`

This file proves results about finite sums over monoids extended by a bottom or top element.
-/

open Finset

variable {ι α : Type*}

namespace WithTop
section AddCommMonoid
variable [AddCommMonoid α] [LT α] {s : Finset ι} {f : ι → WithTop α}

@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithTop α) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
lemma sum_eq_top_iff : ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*]
#align with_top.sum_eq_top_iff WithTop.sum_eq_top_iff

/-- A sum is finite iff all terms are finite. -/
lemma sum_lt_top_iff : ∑ i ∈ s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  simp only [WithTop.lt_top_iff_ne_top, ne_eq, sum_eq_top_iff, not_exists, not_and]
#align with_top.sum_lt_top_iff WithTop.sum_lt_top_iff

/-- A sum of finite terms is finite. -/
lemma sum_lt_top (h : ∀ i ∈ s, f i ≠ ⊤) : ∑ i ∈ s, f i < ⊤ :=
  sum_lt_top_iff.2 fun i hi ↦ WithTop.lt_top_iff_ne_top.2 (h i hi)
#align with_top.sum_lt_top WithTop.sum_lt_top

end AddCommMonoid

/-- A product of finite terms is finite. -/
lemma prod_lt_top [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α] [LT α]
    {s : Finset ι} {f : ι → WithTop α} (h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i ∈ s, f i < ⊤ :=
  prod_induction f (· < ⊤) (fun _ _ h₁ h₂ ↦ mul_lt_top' h₁ h₂) (coe_lt_top 1)
    fun a ha ↦ WithTop.lt_top_iff_ne_top.2 (h a ha)
#align with_top.prod_lt_top WithTop.prod_lt_top

end WithTop

namespace WithBot
section AddCommMonoid
variable [AddCommMonoid α] [LT α] {s : Finset ι} {f : ι → WithBot α}

@[simp, norm_cast] lemma coe_sum (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s, f i = ∑ i ∈ s, (f i : WithBot α) := map_sum addHom f s

/-- A sum is infinite iff one term is infinite. -/
lemma sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

/-- A sum is finite iff all terms are finite. -/
lemma bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, sum_eq_bot_iff, not_exists, not_and]

/-- A sum of finite terms is finite. -/
lemma sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i :=
  bot_lt_sum_iff.2 fun i hi ↦ WithBot.bot_lt_iff_ne_bot.2 (h i hi)
#align with_bot.sum_lt_bot WithBot.sum_lt_bot

end AddCommMonoid

/-- A product of finite terms is finite. -/
lemma prod_lt_bot [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] [DecidableEq α] [LT α]
    {s : Finset ι} {f : ι → WithBot α} (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∏ i ∈ s, f i :=
  prod_induction f (⊥ < ·) (fun _ _ h₁ h₂ ↦ bot_lt_mul' h₁ h₂) (bot_lt_coe 1)
    fun a ha ↦ WithBot.bot_lt_iff_ne_bot.2 (h a ha)
#align with_bot.prod_lt_bot WithBot.prod_lt_bot

end WithBot
