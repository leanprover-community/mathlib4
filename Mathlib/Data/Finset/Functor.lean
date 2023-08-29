/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Scott Morrison
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Multiset.Functor

#align_import data.finset.functor from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

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
  id_map s := image_id
  comp_map f g s := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]
                          -- 🎉 no goals

@[simp]
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.image f := rfl
#align finset.fmap_def Finset.fmap_def

end Functor

/-! ### Pure -/


protected instance pure : Pure Finset :=
  ⟨fun x => {x}⟩

@[simp]
theorem pure_def {α} : (pure : α → Finset α) = singleton := rfl
#align finset.pure_def Finset.pure_def

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
#align finset.seq_def Finset.seq_def

@[simp]
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl
#align finset.seq_left_def Finset.seqLeft_def

@[simp]
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl
#align finset.seq_right_def Finset.seqRight_def

/-- `Finset.image₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image₂_def {α β γ : Type _} (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = f <$> s <*> t := by
  ext
  -- ⊢ a✝ ∈ image₂ f s t ↔ a✝ ∈ Seq.seq (f <$> s) fun x => t
  simp [mem_sup]
  -- 🎉 no goals
#align finset.image₂_def Finset.image₂_def

instance lawfulApplicative : LawfulApplicative Finset :=
  { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def, fmap_def, seqLeft_def]
      -- ⊢ (if t = ∅ then ∅ else s) = sup (image (const β✝) s) fun f => image f t
      obtain rfl | ht := t.eq_empty_or_nonempty
      -- ⊢ (if ∅ = ∅ then ∅ else s) = sup (image (const β✝) s) fun f => image f ∅
      · simp_rw [image_empty, if_true]
        -- ⊢ ∅ = sup (image (const β✝) s) fun f => ∅
        exact (sup_bot _).symm
        -- 🎉 no goals
      · ext a
        -- ⊢ (a ∈ if t = ∅ then ∅ else s) ↔ a ∈ sup (image (const β✝) s) fun f => image f t
        rw [if_neg ht.ne_empty, mem_sup]
        -- ⊢ a ∈ s ↔ ∃ v, v ∈ image (const β✝) s ∧ a ∈ image v t
        refine' ⟨fun ha => ⟨const _ a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, _⟩
        -- ⊢ (∃ v, v ∈ image (const β✝) s ∧ a ∈ image v t) → a ∈ s
        rintro ⟨f, hf, ha⟩
        -- ⊢ a ∈ s
        rw [mem_image] at hf ha
        -- ⊢ a ∈ s
        obtain ⟨b, hb, rfl⟩ := hf
        -- ⊢ a ∈ s
        obtain ⟨_, _, rfl⟩ := ha
        -- ⊢ const β✝ b w✝ ∈ s
        exact hb
        -- 🎉 no goals
    seqRight_eq := fun s t => by
      rw [seq_def, fmap_def, seqRight_def]
      -- ⊢ (if s = ∅ then ∅ else t) = sup (image (const α✝ id) s) fun f => image f t
      obtain rfl | hs := s.eq_empty_or_nonempty
      -- ⊢ (if ∅ = ∅ then ∅ else t) = sup (image (const α✝ id) ∅) fun f => image f t
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
        -- 🎉 no goals
      · ext a
        -- ⊢ (a ∈ if s = ∅ then ∅ else t) ↔ a ∈ sup (image (const α✝ id) s) fun f => imag …
        rw [if_neg hs.ne_empty, mem_sup]
        -- ⊢ a ∈ t ↔ ∃ v, v ∈ image (const α✝ id) s ∧ a ∈ image v t
        refine' ⟨fun ha => ⟨id, mem_image_const_self.2 hs, by rwa [image_id]⟩, _⟩
        -- ⊢ (∃ v, v ∈ image (const α✝ id) s ∧ a ∈ image v t) → a ∈ t
        rintro ⟨f, hf, ha⟩
        -- ⊢ a ∈ t
        rw [mem_image] at hf ha
        -- ⊢ a ∈ t
        obtain ⟨b, hb, rfl⟩ := ha
        -- ⊢ f b ∈ t
        obtain ⟨_, _, rfl⟩ := hf
        -- ⊢ const α✝ id w✝ b ∈ t
        exact hb
        -- 🎉 no goals
    pure_seq := fun f s => by simp only [pure_def, seq_def, sup_singleton, fmap_def]
                              -- 🎉 no goals
    map_pure := fun f a => image_singleton _ _
    seq_pure := fun s a => sup_singleton'' _ _
    seq_assoc := fun s t u => by
      ext a
      -- ⊢ (a ∈ Seq.seq u fun x => Seq.seq t fun x => s) ↔ a ∈ Seq.seq (Seq.seq (comp < …
      simp_rw [seq_def, fmap_def]
      -- ⊢ (a ∈ sup u fun f => image f (sup t fun f => image f s)) ↔ a ∈ sup (sup (imag …
      simp only [exists_prop, mem_sup, mem_image]
      -- ⊢ (∃ v, v ∈ u ∧ ∃ a_1, (∃ v, v ∈ t ∧ ∃ a, a ∈ s ∧ v a = a_1) ∧ v a_1 = a) ↔ ∃  …
      constructor
      -- ⊢ (∃ v, v ∈ u ∧ ∃ a_1, (∃ v, v ∈ t ∧ ∃ a, a ∈ s ∧ v a = a_1) ∧ v a_1 = a) → ∃  …
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        -- ⊢ ∃ v, (∃ v_1, (∃ a, a ∈ u ∧ comp a = v_1) ∧ ∃ a, a ∈ t ∧ v_1 a = v) ∧ ∃ a_1,  …
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        -- 🎉 no goals
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        -- ⊢ ∃ v, v ∈ u ∧ ∃ a_1, (∃ v, v ∈ t ∧ ∃ a, a ∈ s ∧ v a = a_1) ∧ v a_1 = (g ∘ f) a
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }
        -- 🎉 no goals

instance commApplicative : CommApplicative Finset :=
  { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      -- ⊢ Finset.biUnion s ((fun f => image f t) ∘ Prod.mk) = Finset.biUnion t ((fun f …
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [product_eq_biUnion_right]] }
      -- 🎉 no goals

end Applicative

/-! ### Monad -/


section Monad

variable [∀ P, Decidable P]

instance : Monad Finset :=
  { Finset.applicative with bind := sup }

@[simp]
theorem bind_def {α β} : (· >>= ·) = sup (α := Finset α) (β := β) :=
  rfl
#align finset.bind_def Finset.bind_def

instance : LawfulMonad Finset :=
  { Finset.lawfulApplicative with
    bind_pure_comp := fun f s => sup_singleton'' _ _
    bind_map := fun t s => rfl
    pure_bind := fun t s => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, ←sup_biUnion, sup_eq_biUnion, biUnion_biUnion] }
                                  -- 🎉 no goals

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
#align finset.traverse Finset.traverse

@[simp]
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse (pure : α → Id α) s = s := by
  rw [traverse, Multiset.id_traverse]
  -- ⊢ Multiset.toFinset <$> s.val = s
  exact s.val_toFinset
  -- 🎉 no goals
#align finset.id_traverse Finset.id_traverse

open Classical

@[simp]
theorem map_comp_coe (h : α → β) :
    Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun _ => image_toFinset
#align finset.map_comp_coe Finset.map_comp_coe

theorem map_traverse (g : α → G β) (h : β → γ) (s : Finset α) :
    Functor.map h <$> traverse g s = traverse (Functor.map h ∘ g) s := by
  unfold traverse
  -- ⊢ Functor.map h <$> Multiset.toFinset <$> Multiset.traverse g s.val = Multiset …
  simp only [map_comp_coe, functor_norm]
  -- ⊢ (Multiset.toFinset ∘ Functor.map h) <$> Multiset.traverse g s.val = Multiset …
  rw [LawfulFunctor.comp_map, Multiset.map_traverse]
  -- 🎉 no goals
#align finset.map_traverse Finset.map_traverse

end Traversable

end Finset
