import Mathlib.ModelTheory.FinitelyGenerated

/-!
# Partial Isomorphisms and Partial Embeddings

This file defines partial isomorphisms and partial embeddings, and prove simple results.

-/


universe u v w w'

open scoped FirstOrder

open Set

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

variable (M : Type w) (N : Type w') [L.Structure M] [L.Structure N]

namespace Partial

structure PartialIso where
  domain : Set M
  toFun : domain → N
  inj' : Function.Injective toFun
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → M)
    (h : ∀ m, x m ∈ domain) (h' : funMap f x ∈ domain),
    toFun ⟨(funMap f x), h'⟩ = funMap f (toFun ∘ fun m ↦ ⟨x m, h m⟩) := by
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → M) (h : ∀ m, x m ∈ domain),
    RelMap r x → RelMap r (toFun ∘ fun m ↦ ⟨x m, h m⟩) := by
    intros; trivial

structure PartialIso' where
  domain : Set M
  toFun : domain → N
  inj' : Function.Injective toFun
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → domain)
    (h : funMap f ((fun x => x.1) ∘ x) ∈ domain),
    toFun ⟨(funMap f ((fun x => x.1) ∘ x)), h⟩ = funMap f (toFun ∘ x) := by
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → domain),
    RelMap r ((fun x => x.1) ∘ x) → RelMap r (toFun ∘ x) := by
    intros; trivial
