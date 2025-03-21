/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Control.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Notation

/-!
# Functoriality of `Set`

This file defines the functor structure of `Set`.
-/

universe u

open Function Set.Notation

namespace Set

variable {α β : Type u} {s : Set α} {f : α → Set β}

/-- The `Set` functor is a monad.

This is not a global instance because it does not have computational content,
so it does not make much sense using `do` notation in general.
Plus, this would cause monad-related coercions and monad lifting logic to become activated.
Either use `attribute [local instance] Set.monad` to make it be a local instance
or use `SetM.run do ...` when `do` notation is wanted. -/
protected def monad : Monad.{u} Set where
  pure a := {a}
  bind s f := ⋃ i ∈ s, f i
  seq s t := Set.seq s (t ())
  map := Set.image

section with_instance
attribute [local instance] Set.monad

@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl

@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl

@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl

@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl

/-- `Set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image2_def {α β γ : Type u} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by
  ext
  simp

instance : LawfulMonad Set := LawfulMonad.mk'
  (id_map := image_id)
  (pure_bind := biUnion_singleton)
  (bind_assoc := fun _ _ _ => by simp only [bind_def, biUnion_iUnion])
  (bind_pure_comp := fun _ _ => (image_eq_iUnion _ _).symm)
  (bind_map := fun _ _ => seq_def.symm)

instance : CommApplicative (Set : Type u → Type u) :=
  ⟨fun s t => prod_image_seq_comm s t⟩

instance : Alternative Set :=
  { Set.monad with
    orElse := fun s t => s ∪ (t ())
    failure := ∅ }

/-! ### Monadic coercion lemmas -/

variable {β : Set α} {γ : Set β}

theorem mem_coe_of_mem {a : α} (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩

theorem coe_subset : (γ : Set α) ⊆ β := by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert ha

theorem mem_of_mem_coe {a : α} (ha : a ∈ (γ : Set α)) : ⟨a, coe_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert ha

theorem eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe <| hγ.symm ▸ ha

theorem image_coe_eq_restrict_image {δ : Type*} {f : α → δ} : f '' γ = β.restrict f '' γ :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

end with_instance

/-! ### Coercion applying functoriality for `Subtype.val`
The `Monad` instance gives a coercion using the internal function `Lean.Internal.coeM`.
In practice this is only used for applying the `Set` functor to `Subtype.val`,
as was defined in `Data.Set.Notation`. -/

/-- The coercion from `Set.monad` as an instance is equal to the coercion in `Data.Set.Notation`. -/
theorem coe_eq_image_val (t : Set s) :
    @Lean.Internal.coeM Set s α _ Set.monad t = (t : Set α) := by
  change ⋃ (x ∈ t), {x.1} = _
  ext
  simp

variable {β : Set α} {γ : Set β} {a : α}

theorem mem_image_val_of_mem (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ha', rfl⟩

theorem image_val_subset : (γ : Set α) ⊆ β := by
  rintro _ ⟨⟨_, ha⟩, _, rfl⟩; exact ha

theorem mem_of_mem_image_val (ha : a ∈ (γ : Set α)) : ⟨a, image_val_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ha, rfl⟩; exact ha

theorem eq_univ_of_image_val_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val <| hγ.symm ▸ ha

theorem image_image_val_eq_restrict_image {δ : Type*} {f : α → δ} : f '' γ = β.restrict f '' γ := by
  ext; simp

end Set

/-! ### Wrapper to enable the `Set` monad -/

/-- This is `Set` but with a `Monad` instance. -/
def SetM (α : Type u) := Set α

instance : Monad SetM := Set.monad

/-- Evaluates the `SetM` monad, yielding a `Set`.
Implementation note: this is the identity function. -/
protected def SetM.run {α : Type*} (s : SetM α) : Set α := s
