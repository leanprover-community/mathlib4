/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module lean_core.init.data.list.instances
! leanprover-community/lean commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.List.Lemmas

/-!
Decidable Instances for `List` not (yet) in `Std`
-/

universe u

attribute [local simp] List.join List.ret

namespace List

variable {α : Type u} {β : Type v} {γ : Type w}

-- Porting note: simp can prove this
-- @[simp]
theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)
#align list.bind_singleton List.bind_singleton

@[simp] theorem bind_singleton' (l : List α) : (l.bind fun x => [x]) = l := by
  induction l <;> simp [*]
#align list.bind_singleton' List.bind_singleton'

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind fun x => [f x] := by
  simp only [← map_singleton]
  rw [← bind_singleton' l, bind_map, bind_singleton']
#align list.map_eq_bind List.map_eq_bind

theorem bind_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind fun x => (f x).bind g := by induction l <;> simp [*]
#align list.bind_assoc List.bind_assoc

instance instMonad : Monad List.{u} where
  pure := @List.ret
  bind := @List.bind
  map := @List.map
#align list.monad List.instMonad

instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := List.bind_assoc)
  (bind_pure_comp := fun _ _ => (map_eq_bind _ _).symm)
#align list.is_lawful_monad List.instLawfulMonad

instance instAlternative : Alternative List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())
#align list.alternative List.instAlternative

#noalign list.bin_tree_to_list

variable {α : Type u} {p : α → Prop} [DecidablePred p]

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
