/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Init

/-!
# Basic facts about `Thunk`.
-/

namespace Thunk

@[simp] theorem get_pure {α} (x : α) : (Thunk.pure x).get = x := rfl
@[simp] theorem get_mk {α} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

universe u v
variable {α : Type u} {β : Type v}

instance [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

/-- The Cartesian product of two thunks. -/
def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

@[simp] theorem prod_get_fst {a : Thunk α} {b : Thunk β} : (prod a b).get.1 = a.get := rfl
@[simp] theorem prod_get_snd {a : Thunk α} {b : Thunk β} : (prod a b).get.2 = b.get := rfl

/-- The sum of two thunks. -/
def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get

instance [Add α] : Add (Thunk α) := ⟨add⟩

@[simp] theorem add_get [Add α] {a b : Thunk α} : (a + b).get = a.get + b.get := rfl

end Thunk
