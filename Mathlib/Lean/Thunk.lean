/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Mathport.Rename

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
  have ⟨_⟩ := b
  congr
  exact funext fun _ ↦ eq

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

/-- The cartesian product of two thunks. -/
def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

@[simp] theorem prod_get_fst : (prod a b).get.1 = a.get := rfl
@[simp] theorem prod_get_snd : (prod a b).get.2 = b.get := rfl

/-- The sum of two thunks. -/
def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get

instance [Add α] : Add (Thunk α) := ⟨add⟩

@[simp] theorem add_get [Add α] {a b : Thunk α} : (a + b).get = a.get + b.get := rfl

end Thunk
