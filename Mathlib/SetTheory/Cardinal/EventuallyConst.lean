/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Eventually constant monotone functions

This file proves variations of the following theorem: if `α` is a linear order and `β` is a partial
order with `#β < cof α`, then any monotone function `f : α → β` must be eventually constant. In
particular, this applies for functions from `Cardinal.{u}` or `Ordinal.{u}` into a `Small.{u}` type.
-/

public section

universe u v

variable {α : Type u} {β : Type v} [LinearOrder α] [PartialOrder β]

open Cardinal Filter Order Set

theorem eventuallyConst_of_rangeSplitting [Nonempty α] {f : α → β} (hf : Monotone f)
    (hf' : ¬ IsCofinal (range (rangeSplitting f))) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
  refine ⟨i, fun j hij ↦ (hf hij).antisymm' <| (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]

theorem Monotone.eventuallyConst_of_lt_cof {f : α → β} (hf : Monotone f)
    (hα : lift.{u} #β < lift.{v} (cof α)) : atTop.EventuallyConst f := by
  have : Nonempty α := by by_contra!; simp at hα
  apply eventuallyConst_of_rangeSplitting hf
  contrapose! hα
  classical let := hf.linearOrder_range
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα, lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)

theorem Antitone.eventuallyConst_of_lt_cof {f : α → β} (hf : Antitone f)
    (hα : lift.{u} #β < lift.{v} (cof α)) : atTop.EventuallyConst f :=
  hf.dual_right.eventuallyConst_of_lt_cof hα

namespace Cardinal
variable {f : Cardinal.{v} → α} [Small.{v} α]

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  apply hf.eventuallyConst_of_lt_cof
  simpa [← small_iff_lift_mk_lt_univ]

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (α := αᵒᵈ) hf

end Cardinal

namespace Ordinal
variable {f : Ordinal.{v} → α} [Small.{v} α]

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  apply hf.eventuallyConst_of_lt_cof
  simpa [← small_iff_lift_mk_lt_univ]

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (α := αᵒᵈ) hf

end Ordinal
