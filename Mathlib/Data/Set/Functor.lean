/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.set.functor
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Init.Set
import Mathlib.Control.Basic

/-!
# Functoriality of `Set`

This file defines the functor structure of `Set`.
-/

universe u

open Function

namespace Set

variable {α β : Type u} {s : Set α} {f : α → Set β} {g : Set (α → β)}

instance monad : Monad.{u} Set where
  pure a := {a}
  bind s f := ⋃ i ∈ s, f i
  seq s t := Set.seq s (t ())
  map := Set.image

@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl
#align set.bind_def Set.bind_def

@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl
#align set.fmap_eq_image Set.fmap_eq_image

@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl
#align set.seq_eq_set_seq Set.seq_eq_set_seq

@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl
#align set.pure_def Set.pure_def

/-- `Set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image2_def {α β γ : Type _} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by
  ext
  simp
#align set.image2_def Set.image2_def

instance : LawfulMonad Set := LawfulMonad.mk'
  (id_map := image_id)
  (pure_bind := bunionᵢ_singleton)
  (bind_assoc := fun _ _ _ => by simp only [bind_def, bunionᵢ_unionᵢ])
  (bind_pure_comp := fun _ _ => (image_eq_unionᵢ _ _).symm)
  (bind_map := fun _ _ => seq_def.symm)

instance : CommApplicative (Set : Type u → Type u) :=
  ⟨fun s t => prod_image_seq_comm s t⟩

instance : Alternative Set :=
  { Set.monad with
    orElse := fun s t => s ∪ (t ())
    failure := ∅ }

end Set
