/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan, Shreyas Srinivas
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`,
which is the same notion as a relation `V → V → Prop`.
While this might be too simple of a notion to deserve the grandeur of a new definition,
the intention here is to develop relations using the language of graph theory.

Note that in this treatment, a digraph may have self loops.

The type `Digraph V` is structurally equivalent to `Quiver.{0} V`,
but a difference between these is that `Quiver` is a class —
its purpose is to attach a quiver structure to a particular type `V`.
In contrast, for `Digraph V` we are interested in working with the entire lattice
of digraphs on `V`.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

@[expose] public section

open Function

/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
@[ext]
structure Digraph (V : Type*) where
  /-- The vertex set of a digraph. -/
  verts : Set V
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop
  /-- There is no edge of the digraph outside its vertices. -/
  left_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → v ∈ verts := by grind
  /-- There is no edge of the digraph outside its vertices. -/
  right_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → w ∈ verts := by grind

namespace Digraph

variable {V : Type*} {G : Digraph V} {v w : V}

@[grind →]
theorem Adj.left_mem_verts (h : G.Adj v w) : v ∈ G.verts :=
  G.left_mem_verts_of_adj h

@[grind →]
theorem Adj.right_mem_verts (h : G.Adj v w) : w ∈ G.verts :=
  G.right_mem_verts_of_adj h

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation.
-/
@[simps]
def mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := {
    verts := {v | ∃ w, x v w ∨ x w v}
    Adj v w := x v w
  }
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro ⟨_, h⟩
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where
  verts := .univ
  Adj := ⊤

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that there are no vertices and therefore no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges and no vertices.
-/
protected def emptyDigraph (V : Type*) : Digraph V where
  verts := ∅
  Adj _ _ := False

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
def completeBipartite (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  verts := Set.univ

@[deprecated (since := "2026-09-01")] alias completeBipartiteGraph := completeBipartite

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

@[simp] theorem adj_inj {G H : Digraph V} : verts G = verts H ∧ G.Adj = H.Adj ↔ G = H :=
  Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[grind =] theorem le_iff {G H : Digraph V} :
    G ≤ H ↔ G.verts ⊆ H.verts ∧ ∀ ⦃v w⦄, G.Adj v w → H.Adj v w := .rfl

@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The relation that one `Digraph` is a spanning subgraph of another. -/
def IsSpanningSubgraph (x y : Digraph V) : Prop :=
  x ≤ y ∧ x.verts = y.verts

@[grind =]
theorem isSpanningSubgraph_iff {x y : Digraph V} :
    IsSpanningSubgraph x y ↔ x ≤ y ∧ x.verts = y.verts := .rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (Digraph V) where
  max x y := {
    verts := x.verts ∪ y.verts
    Adj v w := x.Adj v w ∨ y.Adj v w
  }

@[grind =]
theorem sup_verts (x y : Digraph V) : (x ⊔ y).verts = x.verts ∪ y.verts := rfl

@[grind =]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := .rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (Digraph V) where
  min x y := {
    verts := x.verts ∩ y.verts
    Adj v w := x.Adj v w ∧ y.Adj v w
  }

@[simp, grind =]
theorem inf_verts (x y : Digraph V) : (x ⊓ y).verts = x.verts ∩ y.verts := rfl

@[simp, grind =]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := .rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance : Compl (Digraph V) where
  compl G := {
    verts := G.verts
    Adj v w := v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w
  }

@[simp] theorem compl_adj {G : Digraph V} {v w : V} :
    Gᶜ.Adj v w ↔ v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w :=
  .rfl

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := {
    verts := x.verts
    Adj v w := x.Adj v w ∧ ¬ y.Adj v w
  }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := .rfl

instance supSet : SupSet (Digraph V) where
  sSup s := {
    verts := {v | ∃ G ∈ s, v ∈ G.verts}
    Adj v w := ∃ G ∈ s, Adj G v w
  }

instance infSet : InfSet (Digraph V) where
  sInf s := {
    verts := {v | ∀ G ∈ s, v ∈ G.verts}
    Adj a b := ∀ ⦃G⦄, G ∈ s → Adj G a b
  }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := .rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b := .rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]

instance : LT (Digraph V) where
  lt G H := G ≤ H ∧ ¬H ≤ G

instance : DistribLattice (Digraph V) :=
  fast_instance% Function.Injective.distribLattice (fun G ↦ (G.verts, G.Adj)) (fun _ _ ↦ by simp)
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp] theorem isSpanningSubgraph_self (G : Digraph V) : IsSpanningSubgraph G G := by
  simp [isSpanningSubgraph_iff]


section SpanningSubgraphs

/-!
In this section we provide the complete boolean algebra for spanning subgraphs
-/

/--
The type of spanning subgraphs of a digraph `G`
-/
def SpanningSubgraph (G : Digraph V) := {H : Digraph V // IsSpanningSubgraph H G}

instance {G : Digraph V} : PartialOrder G.SpanningSubgraph :=
  Subtype.partialOrder _

@[grind =] theorem SpanningSubgraph.le_iff {G : Digraph V} {H K : G.SpanningSubgraph} :
    H ≤ K ↔ H.val ≤ K.val := .rfl

/-- The top subgraph `⊤` -/
instance : OrderTop G.SpanningSubgraph where
  top := ⟨G, by simp⟩
  le_top H := H.prop.left

/-- The bottom subgraph `⊥` -/
instance : OrderBot G.SpanningSubgraph where
  bot : G.SpanningSubgraph := ⟨⟨G.verts, fun _ _ => False, by simp, by simp⟩, by grind⟩
  bot_le := by grind

/-- The complement of a spanning subgraph with respect to its ambient digraph. -/
instance {G : Digraph V} : Compl G.SpanningSubgraph where
  compl H := ⟨{
      verts := H.val.verts
      Adj v w := G.Adj v w ∧ ¬H.val.Adj v w
    }, by grind⟩

/-- The join/union of two spanning subgraphs. -/
instance {G : Digraph V} : Max G.SpanningSubgraph where
  max H₁ H₂ := ⟨max H₁.val H₂.val, by grind⟩

/-- The meet/intersection of two spanning subgraphs. -/
instance : Min G.SpanningSubgraph where
  min H₁ H₂ := ⟨min H₁.val H₂.val, by grind⟩

/-- The supremum of a set of spanning subgraphs. -/
instance : SupSet G.SpanningSubgraph where
  sSup ℋ := ⟨{
      verts := G.verts
      Adj v w := ∃ H ∈ ℋ, H.val.Adj v w
    }, by grind⟩

/-- The infimum of a set of spanning subgraphs. -/
instance : InfSet G.SpanningSubgraph where
  sInf ℋ := ⟨{
      verts := G.verts
      Adj v w := (∀ H ∈ ℋ, H.val.Adj v w) ∧ G.Adj v w
    }, by grind⟩

instance : HImp G.SpanningSubgraph where
  himp H K := Hᶜ ⊔ K

instance : HNot G.SpanningSubgraph where
  hnot H := Hᶜ
instance : SDiff G.SpanningSubgraph where
  sdiff H K := H ⊓ Kᶜ

instance : CompleteAtomicBooleanAlgebra G.SpanningSubgraph := fast_instance% by
  apply Function.Injective.completeAtomicBooleanAlgebra
    (fun (H : G.SpanningSubgraph) (e : {e : V × V // G.Adj e.1 e.2}) ↦ H.val.Adj e.1.1 e.1.2) <;>
    simp [SpanningSubgraph, Function.Injective, funext_iff, Subtype.ext_iff, Digraph.ext_iff,
      Pi.le_def, le_Prop_eq, lt_iff_le_not_ge, Subtype.forall, Prod.forall, SupSet.sSup,
      InfSet.sInf, Top.top, Bot.bot, Compl.compl, HImp.himp, HNot.hnot, SDiff.sdiff, Max.max,
      Min.min, Lattice.inf, SemilatticeSup.sup, SemilatticeInf.inf, imp_iff_not_or] <;> grind

end SpanningSubgraphs

instance Top : Top (Digraph V) where
  top := Digraph.completeDigraph V

instance Bot : Bot (Digraph V) where
  bot := Digraph.emptyDigraph V

@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := .rfl

@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl

@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by
    ext1
    · simp [Set.eq_empty_of_isEmpty]
    · congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
variable [DecidablePred (· ∈ G.verts)] [DecidablePred (· ∈ H.verts)]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w

instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance decidableRelAdjCompl : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w

end Decidable

end Order

end Digraph
