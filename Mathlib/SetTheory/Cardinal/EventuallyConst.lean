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

namespace Filter.EventuallyConst
variable {f : α → β}

theorem of_not_isCofinal_rangeSplitting [Nonempty α] (hf : Monotone f)
    (hf' : ¬ IsCofinal (range (rangeSplitting f))) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
  refine ⟨i, fun j hij ↦ (hf hij).antisymm' <| (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]

theorem of_monotone_of_lt_cof (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f := by
  have : Nonempty α := by by_contra!; simp at hα
  refine .of_not_isCofinal_rangeSplitting hf ?_
  contrapose! hα
  classical let := hf.isChain_range.linearOrder
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα, lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)

theorem of_antitone_of_lt_cof (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f :=
  .of_monotone_of_lt_cof (β := βᵒᵈ) hf.dual_right hα

end Filter.EventuallyConst

namespace Cardinal
variable {f : Cardinal.{v} → β} [Small.{v} β]

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Cardinal

namespace Ordinal
variable {f : Ordinal.{v} → β} [Small.{v} β]

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Ordinal
