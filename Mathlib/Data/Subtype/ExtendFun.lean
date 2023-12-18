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

/-- Extend a function on a subtype of `α` to a function on `α`.

This is similar to `Function.extend`, but differs on two main points: it's computable, and
the function `g`, that maps elements of `α` which are *not* in the subtype,
is given access to a proof of non-membership of its argument in this definition.
 -/
abbrev extendFun (f : Subtype p → β) (g : (a : α) → ¬p a → β) : α → β :=
  Set.piecewiseMem {x | p x} (f ⟨·, ·⟩) g

theorem extend_eq_extendFun (f : Subtype p → β) (g : α → β) :
    Function.extend Subtype.val f g = extendFun f (fun a _ => g a) := by
  funext a
  simp only [Function.extend, Subtype.exists, exists_prop, exists_eq_right, extendFun,
    Set.piecewiseMem, Set.mem_setOf_eq]
  split_ifs with h_pa
  · congr
    have : ∃ (a' : Subtype p), a'.val = a :=
      ⟨⟨a, h_pa⟩, rfl⟩
    rw [← Subtype.val_inj, Classical.choose_spec this]
  · rfl

variable {f : Subtype p → β} {g : (a : α) → ¬p a → β}

lemma extendFun_of_p (a : α) (h : p a) : extendFun f g a = f ⟨a, h⟩ := by
  simp only [extendFun, Set.piecewiseMem, coe_eta, Set.mem_setOf_eq, h, dite_true]

@[simp] lemma extendFun_val (a : Subtype p) :
    extendFun f g a.val = f a :=
  extendFun_of_p a.val a.property

@[simp] lemma extendFun_comp_val : extendFun f g ∘ Subtype.val = f := by
  funext a; rw [Function.comp_apply, extendFun_val]

end Subtype
