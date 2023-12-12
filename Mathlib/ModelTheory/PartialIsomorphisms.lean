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

/-
structure PartialIso where
  domain : Set M
  toFun : domain → N
  inj' : Function.Injective toFun
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → M)
    (h : ∀ m, x m ∈ domain) (h' : funMap f x ∈ domain),
    toFun ⟨(funMap f x), h'⟩ = funMap f (toFun ∘ fun m ↦ ⟨x m, h m⟩) := by
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → M) (h : ∀ m, x m ∈ domain),
    RelMap r x ↔ RelMap r (toFun ∘ fun m ↦ ⟨x m, h m⟩) := by
    intros; trivial
-/

/-- A partial isomorphism of first-order structures is an injective partial map
that commutes with the interpretations of functions and relations -/
structure PartialIso where
  domain : Set M
  toFun : domain → N
  inj' : Function.Injective toFun
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → domain)
    (h : funMap f ((fun x => x.1) ∘ x) ∈ domain),
    toFun ⟨(funMap f ((fun x => x.1) ∘ x)), h⟩ = funMap f (toFun ∘ x) := by
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → domain),
    RelMap r ((fun x => x.1) ∘ x) ↔ RelMap r (toFun ∘ x) := by
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪ₚ[" L "] " B => FirstOrder.Language.PartialIso L A B

namespace Partial

instance hasCoeToFun : CoeFun (M ↪ₚ[L] N) fun f => (f.domain → N) where
  coe := fun (f : M ↪ₚ[L] N) ↦ f.toFun

@[simp]
theorem toFun_eq_coe {f : M ↪ₚ[L] N} : f.toFun = (f : f.domain → N) :=
  rfl

@[ext]
theorem ext ⦃f g : M ↪ₚ[L] N⦄ (h : ∀ {x}, x ∈ f.domain ↔ x ∈ g.domain)
  (h' : ∀ x (u : x ∈ f.domain), f ⟨x, u⟩ = g ⟨x, h.1 u⟩) : f = g := by
  rcases f with ⟨domain, toFun, _⟩
  rcases g with ⟨domain_g, toFun_g, _⟩
  cases Set.ext @h
  cases (funext (fun x ↦ h' x.val x.property) : toFun = toFun_g)
  rfl

