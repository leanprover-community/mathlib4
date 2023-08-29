/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Logic.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.SplitIfs

#align_import logic.lemmas from "leanprover-community/mathlib"@"2ed7e4aec72395b6a7c3ac4ac7873a7a43ead17c"

/-!
# More basic logic properties
A few more logic lemmas. These are in their own file, rather than `Logic.Basic`, because it is
convenient to be able to use the `split_ifs` tactic.
## Implementation notes
We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/


protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq
#align heq.eq HEq.eq
#align eq.heq Eq.heq

variable {α : Sort*} {p q r : Prop} [Decidable p] [Decidable q] {a b c : α}

theorem dite_dite_distrib_left {a : p → α} {b : ¬p → q → α} {c : ¬p → ¬q → α} :
    (dite p a fun hp ↦ dite q (b hp) (c hp)) =
      dite q (fun hq ↦ (dite p a) fun hp ↦ b hp hq) fun hq ↦ (dite p a) fun hp ↦ c hp hq := by
  split_ifs <;> rfl
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align dite_dite_distrib_left dite_dite_distrib_left

theorem dite_dite_distrib_right {a : p → q → α} {b : p → ¬q → α} {c : ¬p → α} :
    dite p (fun hp ↦ dite q (a hp) (b hp)) c =
      dite q (fun hq ↦ dite p (fun hp ↦ a hp hq) c) fun hq ↦ dite p (fun hp ↦ b hp hq) c := by
  split_ifs <;> rfl
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align dite_dite_distrib_right dite_dite_distrib_right

theorem ite_dite_distrib_left {a : α} {b : q → α} {c : ¬q → α} :
    ite p a (dite q b c) = dite q (fun hq ↦ ite p a <| b hq) fun hq ↦ ite p a <| c hq :=
  dite_dite_distrib_left
#align ite_dite_distrib_left ite_dite_distrib_left

theorem ite_dite_distrib_right {a : q → α} {b : ¬q → α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq ↦ ite p (a hq) c) fun hq ↦ ite p (b hq) c :=
  dite_dite_distrib_right
#align ite_dite_distrib_right ite_dite_distrib_right

theorem dite_ite_distrib_left {a : p → α} {b : ¬p → α} {c : ¬p → α} :
    (dite p a fun hp ↦ ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left
#align dite_ite_distrib_left dite_ite_distrib_left

theorem dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬p → α} :
    dite p (fun hp ↦ ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right
#align dite_ite_distrib_right dite_ite_distrib_right

theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left
#align ite_ite_distrib_left ite_ite_distrib_left

theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right
#align ite_ite_distrib_right ite_ite_distrib_right

lemma Prop.forall {f : Prop → Prop} : (∀ p, f p) ↔ f True ∧ f False :=
  ⟨fun h ↦ ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩
                          -- ⊢ f p
                                             -- ⊢ f p
                                                                 -- ⊢ f True
                                                                 -- ⊢ f False
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align Prop.forall Prop.forall

lemma Prop.exists {f : Prop → Prop} : (∃ p, f p) ↔ f True ∨ f False :=
  ⟨fun ⟨p, h⟩ ↦ by refine' (em p).imp _ _ <;> intro H <;> convert h <;> simp [H],
                   -- ⊢ p → f True
                                              -- ⊢ f True
                                              -- ⊢ f False
                                                          -- ⊢ True ↔ p
                                                          -- ⊢ False ↔ p
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
    by rintro (h | h) <;> exact ⟨_, h⟩⟩
       -- ⊢ ∃ p, f p
                          -- 🎉 no goals
                          -- 🎉 no goals
#align Prop.exists Prop.exists
