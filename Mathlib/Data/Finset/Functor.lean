/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Scott Morrison

! This file was ported from Lean 3 source module data.finset.functor
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Finset.NAry
import Mathbin.Data.Multiset.Functor

/-!
# Functoriality of `finset`

This file defines the functor structure of `finset`.

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

/-- Because `finset.image` requires a `decidable_eq` instance for the target type, we can only
construct `functor finset` when working classically. -/
instance : Functor Finset where map α β f s := s.image f

instance : LawfulFunctor Finset where
  id_map α s := image_id
  comp_map α β γ f g s := image_image.symm

@[simp]
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.image f :=
  rfl
#align finset.fmap_def Finset.fmap_def

end Functor

/-! ### Pure -/


instance : Pure Finset :=
  ⟨fun α x => {x}⟩

@[simp]
theorem pure_def {α} : (pure : α → Finset α) = singleton :=
  rfl
#align finset.pure_def Finset.pure_def

/-! ### Applicative functor -/


section Applicative

variable {α β : Type u} [∀ P, Decidable P]

instance : Applicative Finset :=
  { Finset.functor,
    Finset.hasPure with
    seq := fun α β t s => t.sup fun f => s.image f
    seqLeft := fun α β s t => if t = ∅ then ∅ else s
    seqRight := fun α β s t => if s = ∅ then ∅ else t }

@[simp]
theorem seq_def (s : Finset α) (t : Finset (α → β)) : t <*> s = t.sup fun f => s.image f :=
  rfl
#align finset.seq_def Finset.seq_def

@[simp]
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl
#align finset.seq_left_def Finset.seqLeft_def

@[simp]
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl
#align finset.seq_right_def Finset.seqRight_def

/-- `finset.image₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image₂_def {α β γ : Type _} (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = f <$> s <*> t := by
  ext
  simp [mem_sup]
#align finset.image₂_def Finset.image₂_def

instance : LawfulApplicative Finset :=
  {
    Finset.lawfulFunctor with
    seq_left_eq := fun α β s t =>
      by
      rw [seq_def, fmap_def, seq_left_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [if_pos rfl, image_empty]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty, mem_sup]
        refine' ⟨fun ha => ⟨const β a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, _⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := hf
        obtain ⟨_, _, rfl⟩ := ha
        exact hb
    seq_right_eq := fun α β s t =>
      by
      rw [seq_def, fmap_def, seq_right_def]
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
      · ext a
        rw [if_neg hs.ne_empty, mem_sup]
        refine' ⟨fun ha => ⟨id, mem_image_const_self.2 hs, by rwa [image_id]⟩, _⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨_, _, rfl⟩ := hf
        exact hb
    pure_seq_eq_map := fun α β f s => sup_singleton
    map_pure := fun α β f a => image_singleton _ _
    seq_pure := fun α β s a => sup_singleton'' _ _
    seq_assoc := fun α β γ s t u => by
      ext a
      simp_rw [seq_def, fmap_def]
      simp only [exists_prop, mem_sup, mem_image]
      constructor
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance : CommApplicative Finset :=
  { Finset.lawfulApplicative with
    commutative_prod := fun α β s t =>
      by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_bUnion]
      change (s.bUnion fun a => t.image fun b => (a, b)) = t.bUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_bUnion], rw [product_eq_bUnion_right]] <;> congr <;> ext <;>
        simp_rw [mem_image] }

end Applicative

/-! ### Monad -/


section Monad

variable [∀ P, Decidable P]

instance : Monad Finset :=
  { Finset.applicative with bind := fun α β => @sup _ _ _ _ }

@[simp]
theorem bind_def {α β} : (· >>= ·) = @sup (Finset α) β _ _ :=
  rfl
#align finset.bind_def Finset.bind_def

instance : LawfulMonad Finset :=
  {
    Finset.lawfulApplicative with
    bind_pure_comp_eq_map := fun α β f s => sup_singleton'' _ _
    bind_map_eq_seq := fun α β t s => rfl
    pure_bind := fun α β t s => sup_singleton
    bind_assoc := fun α β γ s f g => by
      convert sup_bUnion _ _
      exact sup_eq_bUnion _ _ }

end Monad

/-! ### Alternative functor -/


section Alternative

variable [∀ P, Decidable P]

instance : Alternative Finset :=
  { Finset.applicative with
    orelse := fun α => (· ∪ ·)
    failure := fun α => ∅ }

end Alternative

/-! ### Traversable functor -/


section Traversable

variable {α β γ : Type u} {F G : Type u → Type u} [Applicative F] [Applicative G]
  [CommApplicative F] [CommApplicative G]

/-- Traverse function for `finset`. -/
def traverse [DecidableEq β] (f : α → F β) (s : Finset α) : F (Finset β) :=
  Multiset.toFinset <$> Multiset.traverse f s.1
#align finset.traverse Finset.traverse

@[simp]
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse id.mk s = s :=
  by
  rw [traverse, Multiset.id_traverse]
  exact s.val_to_finset
#align finset.id_traverse Finset.id_traverse

open Classical

@[simp]
theorem map_comp_coe (h : α → β) :
    Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun s => image_toFinset
#align finset.map_comp_coe Finset.map_comp_coe

theorem map_traverse (g : α → G β) (h : β → γ) (s : Finset α) :
    Functor.map h <$> traverse g s = traverse (Functor.map h ∘ g) s :=
  by
  unfold traverse
  simp only [map_comp_coe, functor_norm]
  rw [LawfulFunctor.comp_map, Multiset.map_traverse]
#align finset.map_traverse Finset.map_traverse

end Traversable

end Finset

