/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Init.Set
import Mathlib.Control.Basic

#align_import data.set.functor from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Functoriality of `Set`

This file defines the functor structure of `Set`.
-/

set_option autoImplicit true

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
  -- ⊢ x✝ ∈ image2 f s t ↔ x✝ ∈ Seq.seq (f <$> s) fun x => t
  simp
  -- 🎉 no goals
#align set.image2_def Set.image2_def

instance : LawfulMonad Set := LawfulMonad.mk'
  (id_map := image_id)
  (pure_bind := biUnion_singleton)
  (bind_assoc := fun _ _ _ => by simp only [bind_def, biUnion_iUnion])
                                 -- 🎉 no goals
  (bind_pure_comp := fun _ _ => (image_eq_iUnion _ _).symm)
  (bind_map := fun _ _ => seq_def.symm)

instance : CommApplicative (Set : Type u → Type u) :=
  ⟨fun s t => prod_image_seq_comm s t⟩

instance : Alternative Set :=
  { Set.monad with
    orElse := fun s t => s ∪ (t ())
    failure := ∅ }

/-! ## Monadic coercion lemmas -/

variable {β : Set α} {γ : Set β}

theorem mem_coe_of_mem (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩

theorem coe_subset : (γ : Set α) ⊆ β := by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert ha
  -- ⊢ a✝ ∈ β
                                                 -- 🎉 no goals

theorem mem_of_mem_coe (ha : a ∈ (γ : Set α)) : ⟨a, coe_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert ha
  -- ⊢ { val := a, property := (_ : a ∈ β) } ∈ γ
                                                 -- 🎉 no goals

theorem eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe <| hγ.symm ▸ ha

theorem image_coe_eq_restrict_image {f : α → δ} : f '' γ = β.restrict f '' γ :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

end Set
