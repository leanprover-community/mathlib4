/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Control.AlternativeMonad
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

instance : Alternative Set where
  pure a := {a}
  seq s t := s.seq (t ())
  map := Set.image
  orElse s t := s ∪ t ()
  failure := ∅

@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl

@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl

@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl

@[simp]
theorem failure_def : (failure : Set α) = ∅ :=
  rfl

@[simp]
theorem orElse_def (s : Set α) (t : Set α) : (s <|> t) = s ∪ t :=
  rfl

/-- `Set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image2_def {α β γ : Type u} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by
  ext
  simp

instance : LawfulAlternative Set where
  pure_seq _ _ := Set.singleton_seq
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  map_pure _ _ := Set.image_singleton
  seq_pure _ _ := Set.seq_singleton
  seq_assoc _ _ _ := Set.seq_seq
  map_failure _ := Set.image_empty _
  failure_seq _ := Set.image2_empty_left
  orElse_failure _ := Set.union_empty _
  failure_orElse _ := Set.empty_union _
  orElse_assoc _ _ _ := Set.union_assoc _ _ _ |>.symm
  map_orElse _ _ _ := Set.image_union _ _ _

instance : CommApplicative Set where
  commutative_prod := prod_image_seq_comm

/-- The `Set` functor is a monad.

This is not a global instance because it does not have computational content,
so it does not make much sense using `do` notation in general.

Moreover, this would cause monad-related coercions and monad lifting logic to become activated.
Either use `attribute [local instance] Set.monad` to make it be a local instance
or use `SetM.run do ...` when `do` notation is wanted. -/
protected def monad : AlternativeMonad.{u} Set where
  __ : Alternative Set := inferInstance
  bind s f := ⋃ i ∈ s, f i

section with_instance
attribute [local instance] Set.monad

@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl

instance : LawfulMonad Set where
  bind_pure_comp _ _ := (image_eq_iUnion _ _).symm
  bind_map _ _ := seq_def.symm
  pure_bind := biUnion_singleton
  bind_assoc _ _ _ := by simp only [bind_def, biUnion_iUnion]

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

attribute [local instance] Set.monad in
/-- The coercion from `Set.monad` as an instance is equal to the coercion in `Data.Set.Notation`. -/
theorem coe_eq_image_val (t : Set s) :
    @Lean.Internal.coeM Set s α _ _ t = (t : Set α) := by
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

instance : AlternativeMonad SetM := Set.monad

instance : LawfulMonad SetM := Set.instLawfulMonad

instance : LawfulAlternative SetM := Set.instLawfulAlternative

/-- Evaluates the `SetM` monad, yielding a `Set`.
Implementation note: this is the identity function. -/
protected def SetM.run {α : Type*} (s : SetM α) : Set α := s
