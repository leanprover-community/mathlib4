/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.bool.all_any
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# Boolean quantifiers

This proves a few properties about `list.all` and `list.any`, which are the `bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type _} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

#print List.all_nil /-
@[simp]
theorem all_nil (p : α → Bool) : all [] p = tt :=
  rfl
#align list.all_nil List.all_nil
-/

/- warning: list.all_cons -> List.all_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Bool) (a : α) (l : List.{u1} α), Eq.{1} Bool (List.all.{u1} α (List.cons.{u1} α a l) p) (and (p a) (List.all.{u1} α l p))
but is expected to have type
  forall {α : Type.{u1}} {p : α} {a : List.{u1} α} {l : α -> Bool}, Eq.{1} Bool (List.all.{u1} α (List.cons.{u1} α p a) l) (and (l p) (List.all.{u1} α a l))
Case conversion may be inaccurate. Consider using '#align list.all_cons List.all_consₓ'. -/
@[simp]
theorem all_cons (p : α → Bool) (a : α) (l : List α) : all (a :: l) p = (p a && all l p) :=
  rfl
#align list.all_cons List.all_cons

theorem all_iff_forall {p : α → Bool} : all l p ↔ ∀ a ∈ l, p a :=
  by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
  simp only [all_cons, Bool.and_coe_iff, ih, forall_mem_cons]
#align list.all_iff_forall List.all_iff_forall

theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp only [all_iff_forall, Bool.of_decide_iff]
#align list.all_iff_forall_prop List.all_iff_forall_prop

#print List.any_nil /-
@[simp]
theorem any_nil (p : α → Bool) : any [] p = ff :=
  rfl
#align list.any_nil List.any_nil
-/

/- warning: list.any_cons -> List.any_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Bool) (a : α) (l : List.{u1} α), Eq.{1} Bool (List.any.{u1} α (List.cons.{u1} α a l) p) (or (p a) (List.any.{u1} α l p))
but is expected to have type
  forall {α : Type.{u1}} {p : α} {a : List.{u1} α} {l : α -> Bool}, Eq.{1} Bool (List.any.{u1} α (List.cons.{u1} α p a) l) (or (l p) (List.any.{u1} α a l))
Case conversion may be inaccurate. Consider using '#align list.any_cons List.any_consₓ'. -/
@[simp]
theorem any_cons (p : α → Bool) (a : α) (l : List α) : any (a :: l) p = (p a || any l p) :=
  rfl
#align list.any_cons List.any_cons

theorem any_iff_exists {p : α → Bool} : any l p ↔ ∃ a ∈ l, p a :=
  by
  induction' l with a l ih
  · exact iff_of_false Bool.not_false' (not_exists_mem_nil _)
  simp only [any_cons, Bool.or_coe_iff, ih, exists_mem_cons_iff]
#align list.any_iff_exists List.any_iff_exists

theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp [any_iff_exists]
#align list.any_iff_exists_prop List.any_iff_exists_prop

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_iff_exists.2 ⟨_, h₁, h₂⟩
#align list.any_of_mem List.any_of_mem

end List

