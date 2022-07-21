/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.Init.Data.List.Basic

instance decidableBEx (p : α → Prop) [DecidablePred p] : ∀ l : List α, Decidable (∃ x ∈ l, p x)
| [] => isFalse (fun x => nomatch x)
| x :: xs =>
  if h₁ : p x then isTrue ⟨x, List.Mem.head _ _, h₁⟩ else
    match decidableBEx p xs with
    | isTrue h₂ => isTrue $ match h₂ with | ⟨y, hm, hp⟩ => ⟨y, List.Mem.tail _ hm, hp⟩
    | isFalse h₂ => isFalse fun
      | ⟨y, List.Mem.tail _ h, hp⟩ => h₂ ⟨y, h, hp⟩
      | ⟨_, List.Mem.head _ _, hp⟩ => h₁ hp

instance decidableBAll (p : α → Prop) [DecidablePred p] (l : List α) : Decidable (∀ x ∈ l, p x) :=
  if h : ∃ x ∈ l, ¬p x then isFalse $ let ⟨x, h, np⟩ := h; fun al => np (al x h)
  else isTrue $ fun x hx => if h' : p x then h' else (h ⟨x, hx, h'⟩).elim
