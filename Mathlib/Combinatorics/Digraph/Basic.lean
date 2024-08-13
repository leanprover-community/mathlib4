/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
-/
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Pi

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`. Although the structure is definitionally
equivalent to a `Quiver` in a specialized universe, the intention is to consider graph theory
language as basic. Furthermore, `Digraph` is not intended to be used as a class.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

open Finset Function

/-- A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent. -/
@[ext]
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop

noncomputable instance {V : Type*} [Fintype V] : Fintype (Digraph V) := by
  classical exact Fintype.ofInjective Digraph.Adj (fun _ _ ↦ Digraph.ext)

/-- Constructor for digraphs using a boolean function. -/
@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' := by
    intro adj adj'
    simp only [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr_fun₂ h v w

/-- The complete digraph on a type `V` is the digraph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

/-- The digraph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

/-- Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these. -/
@[simps]
def Digraph.completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

namespace Digraph

variable {ι : Sort*} {V W X : Type*} (G : Digraph V) (G' : Digraph W) {a b c u v w : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) :=
  fun _ _ ↦ Digraph.ext

@[simp]
theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

section Order

/-- The relation that one `Digraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Sup (Digraph V) where
  sup x y :=
    { Adj := x.Adj ⊔ y.Adj }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (Digraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance hasCompl : HasCompl (Digraph V) where
  compl G :=
    { Adj := fun v w ↦ ¬G.Adj v w }

@[simp]
theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s :=
    { Adj := fun a b ↦ ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s :=
    { Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by
  simp [iInf]

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { show DistribLattice (Digraph V) from
      adj_injective.distribLattice _ (fun _ _ ↦ rfl) fun _ _ ↦ rfl with
    le := fun G H ↦ ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeDigraph V
    bot := emptyDigraph V
    le_top := fun x v w _ ↦ trivial
    bot_le := fun x v w h ↦ h.elim
    sdiff_eq := fun x y ↦ by
      ext (v w)
      exact Iff.rfl
    inf_compl_le_bot := fun G v w h ↦ False.elim <| h.2 h.1
    top_le_sup_compl := fun G v w _ ↦ by tauto
    sSup := sSup
    le_sSup := fun s G hG a b hab ↦ ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b ↦ by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab ↦ hab hG
    le_sInf := fun s G hG a b hab ↦ fun H hH ↦ hG _ hH hab
    iInf_iSup_eq := fun f ↦ by ext; simp [Classical.skolem] }

@[simp]
theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp]
theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeDigraph_eq_top (V : Type*) : completeDigraph V = ⊤ :=
  rfl

@[simp]
theorem emptyDigraph_eq_bot (V : Type*) : emptyDigraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type*) : Inhabited (Digraph V) :=
  ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w

instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

end Digraph
