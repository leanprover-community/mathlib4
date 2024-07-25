/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Boolean quantifiers

This proves a few properties about `List.all` and `List.any`, which are the `Bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

-- Porting note: in Batteries

theorem all_iff_forall {p : α → Bool} : all l p ↔ ∀ a ∈ l, p a := by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
  simp only [all_cons, Bool.and_eq_true_iff, ih, forall_mem_cons]

theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp only [all_iff_forall, decide_eq_true_iff]

-- Porting note: in Batteries

theorem any_iff_exists {p : α → Bool} : any l p ↔ ∃ a ∈ l, p a := by
  induction' l with a l ih
  · exact iff_of_false Bool.false_ne_true (not_exists_mem_nil _)
  simp only [any_cons, Bool.or_eq_true_iff, ih, exists_mem_cons_iff]

theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp [any_iff_exists]

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_iff_exists.2 ⟨_, h₁, h₂⟩

end List
