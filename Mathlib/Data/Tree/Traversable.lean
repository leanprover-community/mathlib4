/-
Copyright (c) 2025 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/

import Mathlib.Data.Tree.Basic
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

/-!
# Traversable Binary Tree

Provides a `Traversable` instance for the `Tree` type.
-/

universe u v w

namespace Tree
section Traverse
variable {α β : Type*}

instance : Traversable Tree where
  map := map
  traverse := traverse

lemma comp_traverse
    {F : Type u → Type v} {G : Type v → Type w} [Applicative F] [Applicative G]
    [LawfulApplicative G] {β : Type v} {γ : Type u} (f : β → F γ) (g : α → G β)
    (t : Tree α) : t.traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) =
      Functor.Comp.mk ((·.traverse f) <$> (t.traverse g)) := by
  induction t with
  | nil => rw [traverse, traverse, map_pure, traverse]; rfl
  | node v l r hl hr =>
    rw [traverse, hl, hr, traverse]
    simp only [Function.comp_def, Function.comp_apply, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

lemma traverse_eq_map_id (f : α → β) (t : Tree α) :
    t.traverse ((pure : β → Id β) ∘ f) = pure (t.map f) := by
  induction t with
  | nil => rw [traverse, map]
  | node v l r hl hr =>
    rw [traverse, map, hl, hr, Function.comp_apply, map_pure, pure_seq, map_pure, pure_seq,
      map_pure]

lemma naturality {F G : Type u → Type*} [Applicative F] [Applicative G] [LawfulApplicative F]
    [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Type u} (f : α → F β)
    (t : Tree α) : η (t.traverse f) = t.traverse (η.app β ∘ f : α → G β) := by
  induction t with
  | nil => rw [traverse, traverse, η.preserves_pure]
  | node v l r hl hr =>
    rw [traverse, traverse, η.preserves_seq, η.preserves_seq, η.preserves_map, hl, hr,
      Function.comp_apply]

instance : LawfulTraversable Tree where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η

end Traverse

end Tree
