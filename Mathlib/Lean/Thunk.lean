/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Mathport.Rename
import Std.Tactic.Ext

/-!
# Basic facts about `Thunk`.
-/

set_option autoImplicit true

namespace Thunk

#align thunk.mk Thunk.mk

-- Porting note: Added `Thunk.ext` to get `ext` tactic to work.
@[ext]
theorem ext {α : Type u} {a b : Thunk α} (eq : a.get = b.get) : a = b := by
  have ⟨_⟩ := a
  -- ⊢ { fn := fn✝ } = b
  have ⟨_⟩ := b
  -- ⊢ { fn := fn✝¹ } = { fn := fn✝ }
  congr
  -- ⊢ fn✝¹ = fn✝
  exact funext fun _ ↦ eq
  -- 🎉 no goals

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  -- ⊢ Decidable (a = b)
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  -- ⊢ Decidable (a = b)
  rw [this]
  -- ⊢ Decidable (Thunk.get a = Thunk.get b)
  infer_instance
  -- 🎉 no goals

/-- The product of two thunks. -/
def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

@[simp] theorem prod_get_fst : (prod a b).get.1 = a.get := rfl
@[simp] theorem prod_get_snd : (prod a b).get.2 = b.get := rfl

end Thunk
