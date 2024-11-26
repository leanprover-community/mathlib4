/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.List.Pairwise
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type*} {R : α → α → Prop} {l : List α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  apply Pairwise.forall_of_forall
  · exact fun a b h hne => hR (h hne.symm)
  · exact fun _ _ hx => (hx rfl).elim
  · exact hl.imp (@fun a b h _ => by exact h)

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr

-- Porting note: Duplicate of `pairwise_map` but with `f` explicit.
@[deprecated "No deprecation message was provided." (since := "2024-02-25")]
theorem pairwise_map' (f : β → α) :
    ∀ {l : List β}, Pairwise R (map f l) ↔ Pairwise (R on f) l
  | [] => by simp only [map, Pairwise.nil]
  | b :: l => by
    simp only [map, pairwise_cons, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pairwise_map]

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply hr
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

/-! ### Pairwise filtering -/

protected alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self

end List
