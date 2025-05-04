/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar

/-!
# Boolean quantifiers

This proves a few properties about `List.all` and `List.any`, which are the `Bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp

theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_eq_true.2 ⟨_, h₁, h₂⟩

end List
