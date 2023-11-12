/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic

/-!
This file provides a way to extend a function on a subtype of `α` to a function on `α`
-/

namespace Subtype

variable {α β : Type*} {p : α → Prop} [DecidablePred p]

/-- Extend a function on a subtype of `α` to a function on `α`. -/
abbrev extendFun (f : Subtype p → β) (g : (a : α) → ¬p a → β) : α → β :=
  Set.piecewiseMem {x | p x} (f ⟨·, ·⟩) g

variable {f : Subtype p → β} {g : (a : α) → ¬p a → β}

lemma extendFun_of_p (a : α) (h : p a) : extendFun f g a = f ⟨a, h⟩ := by
  have : a ∈ {x | p x} := h
  simp only [extendFun, Set.piecewiseMem, coe_eta, this, dite_true]

@[simp] lemma extendFun_val (a : Subtype p) :
    extendFun f g a.val = f a :=
  extendFun_of_p a.val a.property

@[simp] lemma extendFun_comp_val : extendFun f g ∘ Subtype.val = f := by
  funext a; rw [Function.comp_apply, extendFun_val]


end Subtype
