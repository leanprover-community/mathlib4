/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Monotone functions from cardinals to small type are eventually constant

We prove variations of the following theorem: if `α` is a `Small.{u}` partially ordered type, and
`f : Cardinal.{u} → α` is a monotone function, then `f` is eventually constant.
-/

public section

universe u

variable {α : Type*} [PartialOrder α] [Small.{u} α]

open Filter Set

namespace Cardinal
variable {f : Cardinal.{u} → α}

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨a, ha⟩ := bddAbove_of_small (range (rangeSplitting f))
  refine ⟨a, fun b hb ↦ (hf hb).antisymm' ?_⟩
  have := hf <| ha (mem_range_self (ι := range f) ⟨f b, b, rfl⟩)
  rwa [apply_rangeSplitting f] at this

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (α := αᵒᵈ) hf

end Cardinal

namespace Ordinal
variable {f : Ordinal.{u} → α}

theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨a, ha⟩ := bddAbove_of_small (range (rangeSplitting f))
  refine ⟨a, fun b hb ↦ (hf hb).antisymm' ?_⟩
  have := hf <| ha (mem_range_self (ι := range f) ⟨f b, b, rfl⟩)
  rwa [apply_rangeSplitting f] at this

theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (α := αᵒᵈ) hf

end Ordinal
