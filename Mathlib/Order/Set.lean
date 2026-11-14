/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

/-! # `Set.range` on `WithBot` and `WithTop` -/

public section

open Set

variable {α β : Type*}

namespace WithBot

@[expose, to_dual]
def toOption (α : Type*) : WithBot α ≃ Option α where
  toFun | bot => none | some x => .some x
  invFun | none => bot | .some x => some x
  left_inv | bot => rfl | some _ => rfl
  right_inv | none => rfl | .some _ => rfl

@[to_dual (attr := simp)] lemma toOption_apply_some (x : α) : toOption α (some x) = .some x := rfl

@[to_dual (attr := simp)] lemma toOption_apply_bot : toOption α bot = none := rfl

@[to_dual (attr := simp)]
lemma toOption_comp_some : (toOption α) ∘ some = Option.some := rfl

@[to_dual (attr := simp)]
lemma symm_toOption_apply_some (x : α) : (toOption α).symm (.some x) = some x := rfl

@[to_dual (attr := simp)]
lemma symm_toOption_apply_none : (toOption α).symm none = bot := rfl

@[to_dual (attr := simp)]
lemma symm_toOption_comp_some : (toOption α).symm ∘ Option.some = some := rfl

@[to_dual]
theorem range_eq (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ WithBot.some : α → β)) := by
  rw [← EquivLike.range_comp f (toOption α).symm, Option.range_eq]
  simp [Function.comp_assoc]
  rfl

end WithBot
