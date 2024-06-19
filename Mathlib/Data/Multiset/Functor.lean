/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
import Mathlib.Data.Multiset.Bind
import Mathlib.Control.Traversable.Lemmas
import Mathlib.Control.Traversable.Instances

#align_import data.multiset.functor from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Functoriality of `Multiset`.
-/


universe u

namespace Multiset

open List

instance functor : Functor Multiset where map := @map

@[simp]
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl
#align multiset.fmap_def Multiset.fmap_def

instance : LawfulFunctor Multiset := by refine' { .. } <;> intros <;> (try simp); rfl

open LawfulTraversable CommApplicative

variable {F : Type u → Type u} [Applicative F] [CommApplicative F]
variable {α' β' : Type u} (f : α' → F β')

/-- Map each element of a `Multiset` to an action, evaluate these actions in order,
    and collect the results.
-/
def traverse : Multiset α' → F (Multiset β') := by
  refine Quotient.lift (Functor.map Coe.coe ∘ Traversable.traverse f) ?_
  introv p; unfold Function.comp
  induction p with
  | nil => rfl
  | @cons x l₁ l₂ _ h =>
    have :
      Multiset.cons <$> f x <*> Coe.coe <$> Traversable.traverse f l₁ =
        Multiset.cons <$> f x <*> Coe.coe <$> Traversable.traverse f l₂ := by rw [h]
    simpa [functor_norm] using this
  | swap x y l =>
    have :
      (fun a b (l : List β') ↦ (↑(a :: b :: l) : Multiset β')) <$> f y <*> f x =
        (fun a b l ↦ ↑(a :: b :: l)) <$> f x <*> f y := by
      rw [CommApplicative.commutative_map]
      congr
      funext a b l
      simpa [flip] using Perm.swap a b l
    simp [(· ∘ ·), this, functor_norm, Coe.coe]
  | trans => simp [*]
#align multiset.traverse Multiset.traverse

instance : Monad Multiset :=
  { Multiset.functor with
    pure := fun x ↦ {x}
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
  (bind_pure_comp := fun _ _ ↦ by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ ↦ by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ ↦ by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

open Functor

open Traversable LawfulTraversable

@[simp]
theorem lift_coe {α β : Type*} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _
#align multiset.lift_coe Multiset.lift_coe

@[simp]
theorem map_comp_coe {α β} (h : α → β) :
    Functor.map h ∘ Coe.coe = (Coe.coe ∘ Functor.map h : List α → Multiset β) := by
  funext; simp only [Function.comp_apply, Coe.coe, fmap_def, map_coe, List.map_eq_map]
#align multiset.map_comp_coe Multiset.map_comp_coe

theorem id_traverse {α : Type*} (x : Multiset α) : traverse (pure : α → Id α) x = x := by
  refine Quotient.inductionOn x ?_
  intro
  simp [traverse, Coe.coe]
#align multiset.id_traverse Multiset.id_traverse

theorem comp_traverse {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (Comp.mk ∘ Functor.map h ∘ g) x =
    Comp.mk (Functor.map (traverse h) (traverse g x)) := by
  refine Quotient.inductionOn x ?_
  intro
  simp only [traverse, quot_mk_to_coe, lift_coe, Coe.coe, Function.comp_apply, Functor.map_map,
    functor_norm]
  simp only [Function.comp, lift_coe]
#align multiset.comp_traverse Multiset.comp_traverse

theorem map_traverse {G : Type* → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → G β) (h : β → γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x := by
  refine Quotient.inductionOn x ?_
  intro
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map, map_comp_coe]
  rw [LawfulFunctor.comp_map, Traversable.map_traverse']
  rfl
#align multiset.map_traverse Multiset.map_traverse

theorem traverse_map {G : Type* → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → β) (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x := by
  refine Quotient.inductionOn x ?_
  intro
  simp only [traverse, quot_mk_to_coe, map_coe, lift_coe, Function.comp_apply]
  rw [← Traversable.traverse_map h g, List.map_eq_map]
#align multiset.traverse_map Multiset.traverse_map

theorem naturality {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x := by
  refine Quotient.inductionOn x ?_
  intro
  simp only [quot_mk_to_coe, traverse, lift_coe, Function.comp_apply,
    ApplicativeTransformation.preserves_map, LawfulTraversable.naturality]
#align multiset.naturality Multiset.naturality

end Multiset
