/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau

! This file was ported from Lean 3 source module data.multiset.functor
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Multiset.Bind
import Mathlib.Control.Traversable.Lemmas
import Mathlib.Control.Traversable.Instances

/-!
# Functoriality of `multiset`.
-/


universe u

namespace Multiset

open List

instance : Functor Multiset where map := @map

@[simp]
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl
#align multiset.fmap_def Multiset.fmap_def

instance : LawfulFunctor Multiset := by refine' { .. } <;> intros <;> simp ; rfl

open IsLawfulTraversable CommApplicative

variable {F : Type u → Type u} [Applicative F] [CommApplicative F]

variable {α' β' : Type u} (f : α' → F β')

def traverse : Multiset α' → F (Multiset β') :=
  Quotient.lift (Functor.map ofList ∘ Traversable.traverse f)
    (by
      introv p; unfold Function.comp
      induction p
      case nil => rfl
      case
        cons x l₁ l₂ _ h =>
        have :
          Multiset.cons <$> f x <*> ofList <$> Traversable.traverse f l₁ =
            Multiset.cons <$> f x <*> ofList <$> Traversable.traverse f l₂ :=
          by rw [h]
        simpa [functor_norm] using this
      case
        swap x y l =>
        have :
          (fun a b (l : List β') => (↑(a :: b :: l) : Multiset β')) <$> f y <*> f x =
            (fun a b l => ↑(a :: b :: l)) <$> f x <*> f y :=
          by
          rw [CommApplicative.commutative_map]
          congr
          funext a b l
          simpa [flip] using Perm.swap a b l
        simp [(· ∘ ·), this, functor_norm]
      case trans => simp [*])
#align multiset.traverse Multiset.traverse

instance : Monad Multiset :=
  { instFunctorMultiset with
    pure := fun x => {x}
    bind := @bind }

@[simp]
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl
#align multiset.pure_def Multiset.pure_def

@[simp]
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl
#align multiset.bind_def Multiset.bind_def

instance : LawfulMonad Multiset := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ => by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ => by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

open Functor

open Traversable IsLawfulTraversable

@[simp]
theorem lift_coe {α β : Type _} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _
#align multiset.lift_coe Multiset.lift_coe

@[simp]
theorem map_comp_coe {α β} (h : α → β) :
    Functor.map h ∘ Coe.coe = (Coe.coe ∘ Functor.map h : List α → Multiset β) := by
  funext ; simp only [Function.comp_apply, Coe.coe, fmap_def, coe_map, List.map_eq_map]
#align multiset.map_comp_coe Multiset.map_comp_coe

theorem id_traverse {α : Type _} (x : Multiset α) : traverse id.mk x = x :=
  Quotient.inductionOn x (by intro ; simp [traverse]; rfl)
#align multiset.id_traverse Multiset.id_traverse

theorem comp_traverse {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (Comp.mk ∘ Functor.map h ∘ g) x = Comp.mk (Functor.map (traverse h) (traverse g x)) :=
  Quotient.inductionOn x
    (by
      intro ; simp [traverse, comp_traverse, functor_norm] ;
        simp [(· <$> ·), (· ∘ ·), functor_norm])
#align multiset.comp_traverse Multiset.comp_traverse

theorem map_traverse {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → G β) (h : β → γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x :=
  Quotient.inductionOn x (by
    intro
    simp [traverse, functor_norm]
    rw [LawfulFunctor.comp_map, map_traverse])
#align multiset.map_traverse Multiset.map_traverse

theorem traverse_map {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → β) (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x :=
  Quotient.inductionOn x (by
    intro
    simp only [traverse, quot_mk_to_coe, coe_map, lift_coe, Function.comp_apply]
    rw [← Traversable.traverse_map h g, List.map_eq_map])
#align multiset.traverse_map Multiset.traverse_map

theorem naturality {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x :=
  Quotient.inductionOn x (by
    intro
    simp [traverse, IsLawfulTraversable.naturality, functor_norm])
#align multiset.naturality Multiset.naturality

end Multiset
