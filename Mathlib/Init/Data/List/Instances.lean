/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Data.List.Lemmas
/-!
Decidable Instances for `List` not (yet) in `Std`
-/

namespace List

variable {α : Type _} {p : α → Prop} [DecidablePred p]

instance decidableBex : ∀ (l : List α), Decidable (∃ x ∈ l, p x)
  | []    => isFalse (by simp)
  | x::xs =>
    if h₁ : p x
    then isTrue ⟨x, mem_cons_self _ _, h₁⟩
    else match decidableBex xs with
      | isTrue h₂  => isTrue <| by
        cases' h₂ with y h; cases' h with hm hp;
        exact ⟨y, mem_cons_of_mem _ hm, hp⟩
      | isFalse h₂ => isFalse <| by
        intro h; cases' h with y h; cases' h with hm hp;
        cases' mem_cons.1 hm with h h
        · rw [h] at hp; contradiction
        · exact absurd ⟨y, h, hp⟩ h₂
#align list.decidable_bex List.decidableBex

instance decidableBall (l : List α) : Decidable (∀ x ∈ l, p x) :=
  if h : ∃ x ∈ l, ¬ p x then
    isFalse $ let ⟨x, h, np⟩ := h; fun al => np (al x h)
  else
    isTrue $ fun x hx => if h' : p x then h' else False.elim $ h ⟨x, hx, h'⟩
#align list.decidable_ball List.decidableBall

end List
