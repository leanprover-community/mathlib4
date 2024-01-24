import Mathlib.ModelTheory.Basic
set_option linter.all false

/-!
# Partial Isomorphisms and Partial Embeddings

This file defines partial isomorphisms and partial embeddings, and prove simple results.

-/


universe u v w w'

open scoped FirstOrder

open Set

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v})

variable (M : Type w) (N : Type w') [L.Structure M] [L.Structure N]

/-- A partial isomorphism of first-order structures is an injective partial map
that commutes with the interpretations of functions and relations -/
structure PartialIso where
  toFun : Set (M × N)
  isFun : ∀ p ∈ toFun, ∀ q ∈ toFun, p.1 = q.1 → p.2 = q.2
  inj' : ∀ p ∈ toFun, ∀ q ∈ toFun, p.2 = q.2 → p.1 = q.1
  map_fun' : ∀ {n} (f : L.Functions n) (x : Fin n → M × N),
    (∀ m, x m ∈ toFun) → funMap f (Prod.fst ∘ x) ∈ image Prod.fst toFun
    → ⟨funMap f (Prod.fst ∘ x), funMap f (Prod.snd ∘ x)⟩ ∈ toFun
  map_rel' : ∀ {n} (r : L.Relations n) (x : Fin n → M × N),
    (∀ m, x m ∈ toFun) → (RelMap r (Prod.fst ∘ x) ↔ RelMap r (Prod.snd ∘ x))


@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪ₚ[" L "] " B => FirstOrder.Language.PartialIso L A B

namespace PartialIso

attribute [coe] PartialIso.toFun

theorem instInhabited' : (∀ r : L.Relations 0, RelMap (M := M) r default ↔ RelMap (M := N) r default)
  → Inhabited (M ↪ₚ[L] N) := by
  intro h
  refine ⟨∅, by tauto, by tauto, by simp, ?_⟩
  intro n r
  cases n <;> simp
  have this1 : RelMap r (Prod.fst (α := M) (β := N) ∘ finZeroElim) = RelMap (M := M) r default
    := by congr ; ext x; exact isEmptyElim x
  have this2 : RelMap r (Prod.snd (α := M) (β := N) ∘ finZeroElim) = RelMap (M := N) r default
    := by congr ; ext x; exact isEmptyElim x
  rw [this1, this2]
  exact h r

noncomputable instance instInhabited : Inhabited (M ↪ₚ[L] M) := instInhabited' L M M (by tauto)

instance instInf : Inf (M ↪ₚ[L] N) := by
  refine
  ⟨ fun f g ↦ ⟨ f.toFun ∩ g.toFun,
    fun p hp q hq ↦ f.isFun p hp.1 q hq.1,
    fun p hp q hq ↦ f.inj' p hp.1 q hq.1,
    ?_,
    ?_,
  ⟩⟩
  intro n F x hx hFx
  have := image_inter_subset Prod.fst f.toFun g.toFun hFx
  simp_rw [mem_inter_iff] at hx this
  exact ⟨f.map_fun' F x (fun m ↦ (hx m).1) this.1,
    g.map_fun' F x (fun m ↦ (hx m).2) this.2⟩
  exact fun _ x hx ↦ f.map_rel' _ x (fun m ↦ ((mem_inter_iff (x m) _ _).2 (hx m)).1)

variable (f : M ↪ₚ[L] N)

def domain : Set M := Prod.fst '' f.toFun

def mem_domain {p : M × N}: p ∈ f.toFun → p.1 ∈ f.domain := fun hp ↦ ⟨p, hp, rfl⟩

def codomain : Set N := Prod.snd '' f.toFun

noncomputable def eval {m : M} : (m ∈ f.domain) → N := fun h ↦ (Classical.choose h).snd

noncomputable def eval_tup {n} {x : Fin n → M} : (∀ m, x m ∈ f.domain) → Fin n → N :=
  fun h m ↦ f.eval (h m)

theorem eval_spec {m : M} (h : m ∈ f.domain) : (m, f.eval h) ∈ f.toFun :=
  (congrFun (congrArg Prod.mk (Classical.choose_spec h).2.symm) (f.eval h)).symm
  ▸ (Classical.choose_spec h).1

theorem eval_tup_spec {n} {x : Fin n → M} (h : ∀ m, x m ∈ f.domain) :
  ∀ m, (x m, f.eval_tup h m) ∈ f.toFun := fun m ↦ f.eval_spec (h m)

@[simp]
theorem eval_is_image {m : M} {n : N} (h : m ∈ f.domain) :
  (m,n) ∈ f.toFun → f.eval h = n := fun h' ↦ f.isFun _ (f.eval_spec h) _ h' rfl

theorem eval_is_eval {m : M} (h h' : m ∈ f.domain) :
  f.eval h = f.eval h' := rfl

@[simp]
theorem map_fun {n} {g : L.Functions n} {x : Fin n → M} (h : ∀ m, x m ∈ f.domain)
  (h' : funMap g x ∈ f.domain) : f.eval h' = funMap g (f.eval_tup h) :=
  f.eval_is_image h' (f.map_fun' g (fun m ↦ (x m, f.eval (h m))) (f.eval_tup_spec h) h')

@[simp]
theorem eval_eq_coe_constants {c : L.Constants} (h : ↑c ∈ f.domain) :
  f.eval h = c := by
  rw [f.map_fun (n := 0) isEmptyElim h]
  exact funMap_eq_coe_constants

theorem map_rel {n} {r : L.Relations n} {x : Fin n → M} (h : ∀ m, x m ∈ f.domain) :
  RelMap r x ↔ RelMap r (f.eval_tup h) :=
  f.map_rel' r (fun m ↦ (x m, f.eval (h m))) (f.eval_tup_spec h)

noncomputable instance hasCoeToFun : CoeFun (M ↪ₚ[L] N) fun f ↦ {m : M} → (m ∈ f.domain) → N where
  coe := fun (f : M ↪ₚ[L] N) ↦ f.eval

@[ext]
theorem ext {f g : M ↪ₚ[L] N} : f.toFun = g.toFun → f = g := by
  intro h
  rcases f with ⟨toFun, _⟩
  cases h
  rfl

@[ext]
theorem ext' ⦃f g : M ↪ₚ[L] N⦄ (h : f.domain = g.domain)
  (h' : ∀ x (u : x ∈ f.domain), f.eval u = g.eval (h ▸ u)) : f = g := by
  apply ext
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

instance instSetLike : SetLike (L.PartialIso M N) (M × N) := ⟨PartialIso.toFun, fun p _ h ↦ p.ext h⟩
