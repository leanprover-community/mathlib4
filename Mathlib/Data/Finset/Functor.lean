/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kim Morrison
-/
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Multiset.Functor

/-!
# Functoriality of `Finset`

This file defines the functor structure of `Finset`.

## TODO

Currently, all instances are classical because the functor classes want to run over all types. If
instead we could state that a functor is lawful/applicative/traversable... between two given types,
then we could provide the instances for types with decidable equality.
-/


universe u

open Function

namespace Finset

/-! ### Functor -/

section Functor

variable {α β : Type u} [∀ P, Decidable P]

/-- Because `Finset.image` requires a `DecidableEq` instance for the target type, we can only
construct `Functor Finset` when working classically. -/
protected instance functor : Functor Finset where map f s := s.image f

instance lawfulFunctor : LawfulFunctor Finset where
  id_map _ := image_id
  comp_map _ _ _ := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.image f := rfl

end Functor

/-! ### Pure -/


protected instance pure : Pure Finset :=
  ⟨fun x => {x}⟩

@[simp]
theorem pure_def {α} : (pure : α → Finset α) = singleton := rfl

/-! ### Applicative functor -/


section Applicative

variable {α β : Type u} [∀ P, Decidable P]

protected instance applicative : Applicative Finset :=
  { Finset.functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

@[simp]
theorem seq_def (s : Finset α) (t : Finset (α → β)) : t <*> s = t.sup fun f => s.image f :=
  rfl

@[simp]
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl

@[simp]
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl

/-- `Finset.image₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image₂_def {α β γ : Type u} (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = f <$> s <*> t := by
  ext
  simp [mem_sup]

instance lawfulApplicative : LawfulApplicative Finset :=
  { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def, fmap_def, seqLeft_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [image_empty, if_true]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty, mem_sup]
        refine ⟨fun ha => ⟨const _ a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := hf
        obtain ⟨_, _, rfl⟩ := ha
        exact hb
    seqRight_eq := fun s t => by
      rw [seq_def, fmap_def, seqRight_def]
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
      · ext a
        rw [if_neg hs.ne_empty, mem_sup]
        refine ⟨fun ha => ⟨id, mem_image_const_self.2 hs, by rwa [image_id]⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨_, _, rfl⟩ := hf
        exact hb
    pure_seq := fun f s => by simp only [pure_def, seq_def, sup_singleton, fmap_def]
    map_pure := fun _ _ => image_singleton _ _
    seq_pure := fun _ _ => sup_singleton_apply _ _
    seq_assoc := fun s t u => by
      ext a
      simp_rw [seq_def, fmap_def]
      simp only [exists_prop, mem_sup, mem_image]
      constructor
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }

instance commApplicative : CommApplicative Finset :=
  { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [product_eq_biUnion_right]] }

end Applicative

/-! ### Monad -/


section Monad

variable [∀ P, Decidable P]

instance : Monad Finset :=
  { Finset.applicative with bind := sup }

@[simp]
theorem bind_def {α β} : (· >>= ·) = sup (α := Finset α) (β := β) :=
  rfl

instance : LawfulMonad Finset :=
  { Finset.lawfulApplicative with
    bind_pure_comp := fun _ _ => sup_singleton_apply _ _
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, ← sup_biUnion, sup_eq_biUnion, biUnion_biUnion] }

end Monad

/-! ### Alternative functor -/


section Alternative

variable [∀ P, Decidable P]

instance : Alternative Finset :=
  { Finset.applicative with
    orElse := fun s t => (s ∪ t ())
    failure := ∅ }

end Alternative

/-! ### Traversable functor -/


section Traversable

variable {α β γ : Type u} {F G : Type u → Type u} [Applicative F] [Applicative G]
  [CommApplicative F] [CommApplicative G]

/-- Traverse function for `Finset`. -/
def traverse [DecidableEq β] (f : α → F β) (s : Finset α) : F (Finset β) :=
  Multiset.toFinset <$> Multiset.traverse f s.1

@[simp]
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse (pure : α → Id α) s = pure s := by
  rw [traverse, Multiset.id_traverse]
  exact s.val_toFinset

open scoped Classical in
@[simp]
theorem map_comp_coe (h : α → β) :
    Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun _ => image_toFinset

open scoped Classical in
@[simp]
theorem map_comp_coe_apply (h : α → β) (s : Multiset α) :
    s.toFinset.image h = (h <$> s).toFinset :=
  congrFun (map_comp_coe h) s

open scoped Classical in
theorem map_traverse (g : α → G β) (h : β → γ) (s : Finset α) :
    Functor.map h <$> traverse g s = traverse (Functor.map h ∘ g) s := by
  unfold traverse
  simp only [Functor.map_map, fmap_def, map_comp_coe_apply, Multiset.fmap_def, ←
    Multiset.map_traverse]

end Traversable

end Finset
