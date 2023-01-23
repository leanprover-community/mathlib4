/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau

! This file was ported from Lean 3 source module data.multiset.functor
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Bind
import Mathbin.Control.Traversable.Lemmas
import Mathbin.Control.Traversable.Instances

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

instance : LawfulFunctor Multiset := by refine' { .. } <;> intros <;> simp

open IsLawfulTraversable CommApplicative

variable {F : Type u → Type u} [Applicative F] [CommApplicative F]

variable {α' β' : Type u} (f : α' → F β')

def traverse : Multiset α' → F (Multiset β') :=
  Quotient.lift (Functor.map coe ∘ Traversable.traverse f)
    (by
      introv p; unfold Function.comp
      induction p
      case nil => rfl
      case
        cons =>
        have :
          Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₁ =
            Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₂ :=
          by rw [p_ih]
        simpa [functor_norm]
      case
        swap =>
        have :
          (fun a b (l : List β') => (↑(a :: b :: l) : Multiset β')) <$> f p_y <*> f p_x =
            (fun a b l => ↑(a :: b :: l)) <$> f p_x <*> f p_y :=
          by
          rw [CommApplicative.commutative_map]
          congr
          funext a b l
          simpa [flip] using perm.swap b a l
        simp [(· ∘ ·), this, functor_norm]
      case trans => simp [*])
#align multiset.traverse Multiset.traverse

instance : Monad Multiset :=
  { Multiset.functor with
    pure := fun α x => {x}
    bind := @bind }

@[simp]
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl
#align multiset.pure_def Multiset.pure_def

@[simp]
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl
#align multiset.bind_def Multiset.bind_def

instance : LawfulMonad Multiset
    where
  bind_pure_comp_eq_map α β f s := Multiset.induction_on s rfl fun a s ih => by simp
  pure_bind α β x f := by simp [pure]
  bind_assoc := @bind_assoc

open Functor

open Traversable IsLawfulTraversable

@[simp]
theorem lift_coe {α β : Type _} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk'' _ _ _
#align multiset.lift_coe Multiset.lift_coe

@[simp]
theorem map_comp_coe {α β} (h : α → β) :
    Functor.map h ∘ coe = (coe ∘ Functor.map h : List α → Multiset β) := by
  funext <;> simp [Functor.map]
#align multiset.map_comp_coe Multiset.map_comp_coe

theorem id_traverse {α : Type _} (x : Multiset α) : traverse id.mk x = x :=
  Quotient.inductionOn x (by intro ; simp [traverse]; rfl)
#align multiset.id_traverse Multiset.id_traverse

theorem comp_traverse {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (comp.mk ∘ Functor.map h ∘ g) x = Comp.mk (Functor.map (traverse h) (traverse g x)) :=
  Quotient.inductionOn x
    (by
      intro <;> simp [traverse, comp_traverse, functor_norm] <;>
        simp [(· <$> ·), (· ∘ ·), functor_norm])
#align multiset.comp_traverse Multiset.comp_traverse

theorem map_traverse {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → G β) (h : β → γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse, functor_norm] <;> rw [LawfulFunctor.comp_map, map_traverse])
#align multiset.map_traverse Multiset.map_traverse

theorem traverse_map {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → β) (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse] <;> rw [← Traversable.traverse_map h g] <;> [rfl, infer_instance])
#align multiset.traverse_map Multiset.traverse_map

theorem naturality {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse, IsLawfulTraversable.naturality, functor_norm])
#align multiset.naturality Multiset.naturality

end Multiset

