/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Functor

/-!
# LawfulTraversable instances

This file provides instances of `LawfulTraversable` for types from the core library: `Option`,
`List` and `Sum`.
-/


universe u v

section Option

open Functor

variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]
variable [LawfulApplicative G]

theorem Option.id_traverse {α} (x : Option α) : Option.traverse (pure : α → Id α) x = pure x := by
  cases x <;> rfl

theorem Option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Option α) :
    Option.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
      Comp.mk (Option.traverse f <$> Option.traverse g x) := by
  cases x <;> (simp [Option.traverse, Option.mapM, functor_norm] <;> rfl)

theorem Option.traverse_eq_map_id {α β} (f : α → β) (x : Option α) :
    Option.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by cases x <;> rfl

variable (η : ApplicativeTransformation F G)

theorem Option.naturality [LawfulApplicative F] {α β} (f : α → F β) (x : Option α) :
    η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x := by
  rcases x with - | x <;> simp! [*, functor_norm, Option.traverse]

end Option

instance : LawfulTraversable Option :=
  { show LawfulMonad Option from inferInstance with
    id_traverse := Option.id_traverse
    comp_traverse := Option.comp_traverse
    traverse_eq_map_id := Option.traverse_eq_map_id
    naturality := fun η _ _ f x => Option.naturality η f x }

namespace List

variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]

section

variable [LawfulApplicative G]

open Applicative Functor List

protected theorem id_traverse {α} (xs : List α) : (List.traverse pure xs : Id _) = pure xs := by
  induction xs <;> simp! [*, List.traverse, functor_norm]

protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : List α) :
    List.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk (List.traverse f <$> List.traverse g x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl

protected theorem traverse_eq_map_id {α β} (f : α → β) (x : List α) :
    List.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm]

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)

protected theorem naturality {α β} (f : α → F β) (x : List α) :
    η (List.traverse f x) = List.traverse (@η _ ∘ f) x := by
  induction x <;> simp! [*, functor_norm]

instance : LawfulTraversable.{u} List :=
  { show LawfulMonad List from inferInstance with
    id_traverse := List.id_traverse
    comp_traverse := List.comp_traverse
    traverse_eq_map_id := List.traverse_eq_map_id
    naturality := List.naturality }

end

section Traverse

variable {α' β' : Type u} (f : α' → F β')

@[simp]
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl

@[simp]
theorem traverse_cons (a : α') (l : List α') :
    traverse f (a :: l) = (· :: ·) <$> f a <*> traverse f l :=
  rfl

variable [LawfulApplicative F]

@[simp]
theorem traverse_append :
    ∀ as bs : List α', traverse f (as ++ bs) = (· ++ ·) <$> traverse f as <*> traverse f bs
  | [], bs => by simp [functor_norm]
  | a :: as, bs => by simp [traverse_append as bs, functor_norm]; congr

theorem mem_traverse {f : α' → Set β'} :
    ∀ (l : List α') (n : List β'), n ∈ traverse f l ↔ Forall₂ (fun b a => b ∈ f a) n l
  | [], [] => by simp
  | a :: as, [] => by simp
  | [], b :: bs => by simp
  | a :: as, b :: bs => by simp [mem_traverse as bs]

end Traverse

end List

namespace Sum

section Traverse

variable {σ : Type u}
variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]

open Applicative Functor

protected theorem traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : σ ⊕ α) :
    Sum.traverse f (g <$> x) = Sum.traverse (f ∘ g) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> rfl

protected theorem id_traverse {σ α} (x : σ ⊕ α) :
    Sum.traverse (pure : α → Id α) x = x := by cases x <;> rfl

variable [LawfulApplicative G]

protected theorem comp_traverse {α β γ : Type u} (f : β → F γ) (g : α → G β) (x : σ ⊕ α) :
    Sum.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk.{u} (Sum.traverse f <$> Sum.traverse g x) := by
  cases x <;> (simp! [Sum.traverse, map_id, functor_norm] <;> rfl)

protected theorem traverse_eq_map_id {α β} (f : α → β) (x : σ ⊕ α) :
    Sum.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl

protected theorem map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : σ ⊕ α) :
    (f <$> ·) <$> Sum.traverse g x = Sum.traverse (f <$> g ·) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> congr

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)

protected theorem naturality {α β} (f : α → F β) (x : σ ⊕ α) :
    η (Sum.traverse f x) = Sum.traverse (@η _ ∘ f) x := by
  cases x <;> simp! [Sum.traverse, functor_norm]

end Traverse

instance {σ : Type u} : LawfulTraversable.{u} (Sum σ) :=
  { show LawfulMonad (Sum σ) from inferInstance with
    id_traverse := Sum.id_traverse
    comp_traverse := Sum.comp_traverse
    traverse_eq_map_id := Sum.traverse_eq_map_id
    naturality := Sum.naturality }

end Sum
