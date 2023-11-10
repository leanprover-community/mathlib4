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

def extendFun (f : Subtype p → β) (g : (a : α) → ¬p a → β) : α → β :=
  Set.piecewiseMem {x | p x} (f ⟨·, ·⟩) g

variable {f : Subtype p → β} (g : (a : α) → ¬p a → β)

@[simp] lemma extendFun_val {a : Subtype p} :
    extendFun f g a.val = f a := by
  have : ↑a ∈ {x | p x} := by exact a.property
  simp only [extendFun, Set.piecewiseMem, coe_eta, this, dite_true]

end Subtype
