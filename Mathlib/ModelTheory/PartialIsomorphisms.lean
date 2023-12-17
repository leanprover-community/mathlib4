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
  toFun : Set (M × N)
  isFun : ∀ p ∈ toFun, ∀ q ∈ toFun, p.1 = q.1 → p.2 = q.2
  inj' : ∀ p ∈ toFun, ∀ q ∈ toFun, p.2 = q.2 → p.1 = q.1
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → M × N),
    ∀ m, x m ∈ toFun → funMap f (Prod.fst ∘ x) ∈ image Prod.fst toFun
    → ⟨funMap f (Prod.fst ∘ x), funMap f (Prod.snd ∘ x)⟩ ∈ toFun
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → M × N),
    RelMap r (Prod.fst ∘ x) ↔ RelMap r (Prod.snd ∘ x)


@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪ₚ[" L "] " B => FirstOrder.Language.PartialIso L A B

namespace PartialIso

def domain : (M ↪ₚ[L] N) → Set M := fun f ↦ image Prod.fst f.toFun

def mem_domain (f : M ↪ₚ[L] N) {p : M × N}: p ∈ f.toFun → p.1 ∈ f.domain := fun hp ↦ ⟨p, hp, rfl⟩

def codomain : (M ↪ₚ[L] N) → Set N := fun f ↦ image Prod.snd f.toFun

noncomputable def eval (f : M ↪ₚ[L] N) {m : M} : (m ∈ f.domain) → N := by intro h ; exact (Classical.choose h).snd

theorem eval_spec (f : M ↪ₚ[L] N) {m : M} (h : m ∈ f.domain) : (m, f.eval h) ∈ f.toFun :=
  (congrFun (congrArg Prod.mk (Classical.choose_spec h).2.symm) (f.eval h)).symm
  ▸ (Classical.choose_spec h).1

theorem eval_is_image {f : M ↪ₚ[L] N} {m : M} {n : N} (h : m ∈ f.domain) :
  (m,n) ∈ f.toFun → f.eval h = n := fun h' ↦ f.isFun _ (f.eval_spec h) _ h' rfl

theorem eval_is_eval {f : M ↪ₚ[L] N} {m : M} (h h' : m ∈ f.domain) :
  f.eval h = f.eval h' := rfl

noncomputable instance hasCoeToFun : CoeFun (M ↪ₚ[L] N) fun f ↦ {m : M} → (m ∈ f.domain) → N where
  coe := fun (f : M ↪ₚ[L] N) ↦ f.eval

@[ext]
theorem ext ⦃f g : M ↪ₚ[L] N⦄ (h : f.domain = g.domain)
  (h' : ∀ x (u : x ∈ f.domain), f.eval u = g.eval (h ▸ u)) : f = g := by
  have : f.toFun = g.toFun := by
    apply Set.ext
    rintro ⟨m, n⟩
    constructor
    intro hmn
    have := g.eval_spec (h ▸ f.mem_domain hmn)
    rw [←(h' m (f.mem_domain hmn)), f.eval_is_image ⟨(m,n), hmn, rfl⟩ hmn] at this
    exact this
    intro hmn
    have := f.eval_spec (h.symm ▸ g.mem_domain hmn)
    rw [(h' m (h.symm ▸ g.mem_domain hmn)), g.eval_is_image ⟨(m,n), hmn, rfl⟩ hmn] at this
    exact this

  rcases f with ⟨toFun, isFun, _⟩
  cases this
  rfl
