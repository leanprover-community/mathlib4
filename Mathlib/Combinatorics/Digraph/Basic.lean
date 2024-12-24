/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
-/
import Mathlib.Combinatorics.Graph.Classes
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Pi

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

open Finset Function Graph

/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
-- @[ext] -- I think we need to remove this ext in favor of the HasAdj ext
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  protected Adj : V → V → Prop

-- 2023
instance {V : Type*} : HasAdj (Digraph V) (fun _ ↦ V) where
  Adj G := G.Adj

-- 2023
/- Perhaps there is an elaborator/delaborator that could help here. -/
@[simp] theorem Digraph.adj_eq_adj {V : Type*} (G : Digraph V) : G.Adj = Adj G := rfl

/-
Digraph.Simps.Adj and initialize_simps_projections were from the 2023 file, not sure if they are
still needed
-/
/-- See Note [custom simps projection] -/
def Digraph.Simps.Adj {V : Type*} (G : Digraph V) : V → V → Prop := Graph.Adj G

initialize_simps_projections Digraph

-- 2023
@[simp]
theorem Digraph.Adj_mk {V : Type*} (adj : V → V → Prop) : Adj (Digraph.mk adj) = adj := rfl

-- 2023
@[ext]
protected theorem Digraph.ext {V : Type*} (G H : Digraph V) : Adj G = Adj H → G = H := by
  cases G; cases H; simp

/--
Constructor for digraphs using a boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
-/
@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Adj (Digraph.mk' adj)) :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)

instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
  Fintype.ofBijective Digraph.mk' <| by
    classical
    refine ⟨Embedding.injective _, ?_⟩
    intro G
    use fun v w ↦ Adj G v w
    ext v w
    simp

namespace Digraph

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges.
-/
protected def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := Digraph.ext

@[simp] theorem adj_inj {G H : Digraph V} : Adj G = Adj H ↔ G = H := Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a spanning subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, Adj x v w → Adj y v w

instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

-- 2023
@[simp] theorem adj_le_iff {G H : Digraph V} : Adj G ≤ Adj H ↔ G ≤ H := Iff.rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (Digraph V) where
  max x y := { Adj := Adj x ⊔ Adj y }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : Adj (x ⊔ y) v w ↔ Adj x v w ∨ Adj y v w := Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (Digraph V) where
  min x y := { Adj := Adj x ⊓ Adj y }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : Adj (x ⊓ y) v w ↔ Adj x v w ∧ Adj y v w := Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance hasCompl : HasCompl (Digraph V) where
  compl G := { Adj := fun v w ↦ ¬Adj G v w }

@[simp] theorem compl_adj (G : Digraph V) (v w : V) : Adj Gᶜ v w ↔ ¬Adj G v w := Iff.rfl

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := { Adj := Adj x \ Adj y }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : Adj (x \ y) v w ↔ Adj x v w ∧ ¬Adj y v w := Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s := { Adj := fun a b ↦ ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s := { Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} : Adj (sSup s) a b ↔ ∃ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : Adj (sInf s) a b ↔ ∀ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : Adj (⨆ i, f i) a b ↔ ∃ i, Adj (f i) a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : Adj (⨅ i, f i) a b ↔ (∀ i, Adj (f i) a b) := by simp [iInf]

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, Adj G a b → Adj H a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { adj_injective.distribLattice Adj (fun _ _ ↦ rfl) fun _ _ ↦ rfl with
    le := fun G H ↦ ∀ ⦃a b⦄, Adj G a b → Adj H a b }

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := Digraph.completeDigraph V
    bot := Digraph.emptyDigraph V
    le_top := fun _ _ _ _ ↦ trivial
    bot_le := fun _ _ _ h ↦ h.elim
    sdiff_eq := fun _ _ ↦ rfl
    inf_compl_le_bot := fun _ _ _ h ↦ absurd h.1 h.2
    top_le_sup_compl := fun G v w _ ↦ by tauto
    sSup := sSup
    le_sSup := fun _ G hG _ _ hab ↦ ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b ↦ by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun _ _ hG _ _ hab ↦ hab hG
    le_sInf := fun _ _ hG _ _ hab ↦ fun _ hH ↦ hG _ hH hab
    iInf_iSup_eq := fun f ↦ by ext; simp [Classical.skolem] }

@[simp] theorem top_adj (v w : V) : Adj (⊤ : Digraph V) v w := trivial

@[simp] theorem bot_adj (v w : V) : Adj (⊥ : Digraph V) v w ↔ False := Iff.rfl

@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl

@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (Adj · v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel (Adj G)] [DecidableRel (Adj H)]

instance Bot.adjDecidable : DecidableRel (Adj (⊥ : Digraph V)) :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False

instance Sup.adjDecidable : DecidableRel (Adj (G ⊔ H)) :=
  inferInstanceAs <| DecidableRel fun v w ↦ (Adj G) v w ∨ (Adj H) v w

instance Inf.adjDecidable : DecidableRel (Adj (G ⊓ H)) :=
  inferInstanceAs <| DecidableRel fun v w ↦ (Adj G) v w ∧ (Adj H) v w

instance SDiff.adjDecidable : DecidableRel (Adj (G \ H)) :=
  inferInstanceAs <| DecidableRel fun v w ↦ Adj G v w ∧ ¬Adj H v w

instance Top.adjDecidable : DecidableRel (Adj (⊤ : Digraph V)) :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance Compl.adjDecidable : DecidableRel (Adj Gᶜ) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬Adj G v w

end Decidable

end Order

end Digraph
