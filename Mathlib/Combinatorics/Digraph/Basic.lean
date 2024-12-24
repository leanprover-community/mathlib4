/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
-/
import Mathlib.Combinatorics.Graph.Hom
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

variable {ι : Sort*} {V W X : Type*} {a b : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := Digraph.ext

@[simp] theorem adj_inj {G H : Digraph V} : Adj G = Adj H ↔ G = H := Digraph.ext_iff.symm

section Order

variable (G : Digraph V)

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

-- Everything past this point has been imported from the 2023 Digraph API

/-- Known as the *transpose* of a digraph, this is the digraph with all edges having
reversed orientation. -/
protected def inv (G : Digraph V) : Digraph V := ⟨flip <| Adj G⟩

-- pp_extended_field_notation Digraph.inv

@[simp] theorem Adj_inv {G : Digraph V} {v w : V} : Adj G.inv v w ↔ Adj G w v := by cases G; rfl

@[simp] theorem inv_inv {G : Digraph V} : G.inv.inv = G := by ext; rfl

@[simp] theorem inv_le_inv {G H : Digraph V} : G.inv ≤ H.inv ↔ G ≤ H :=
  ⟨fun h _ _ h' ↦ h h', fun h _ _ h' ↦ h h'⟩

@[simp] theorem inv_top : (⊤ : Digraph V).inv = ⊤ := rfl
@[simp] theorem inv_bot : (⊥ : Digraph V).inv = ⊥ := rfl

section InAndOutSupport

variable (G : Digraph V)

/-- `G.inSupport` is the set of vertices `v` such that there exists a `w` with `Adj G v w`. -/
protected def inSupport : Set V := Rel.dom (Adj G)

/-- `G.outSupport` is the set of vertices `v` such that there exists a `w` with `Adj G w v`. -/
protected def outSupport : Set V := Rel.codom (Adj G)

-- pp_extended_field_notation Digraph.inSupport
-- pp_extended_field_notation Digraph.outSupport

@[simp] theorem mem_inSupport {v : V} : v ∈ G.inSupport ↔ ∃ w, Adj G v w := Iff.rfl
@[simp] theorem mem_outSupport {v : V} : v ∈ G.outSupport ↔ ∃ w, Adj G w v := Iff.rfl

@[mono]
theorem inSupport_mono {G G' : Digraph V} (h : G ≤ G') : G.inSupport ⊆ G'.inSupport :=
  Rel.dom_mono h

@[mono]
theorem outSupport_mono {G G' : Digraph V} (h : G ≤ G') : G.outSupport ⊆ G'.outSupport :=
  fun _ ⟨w, h'⟩ => ⟨w, h h'⟩

/-- `G.inNeighborSet v` is the set of vertices that are adjacent *to* `v`. -/
protected def inNeighborSet (v : V) : Set V := {w | Adj G w v}

/-- `G.outNeighborSet v` is the set of vertices that `v` is adjacent *to*. -/
protected def outNeighborSet (v : V) : Set V := {w | Adj G v w}

-- pp_extended_field_notation Digraph.inNeighborSet
-- pp_extended_field_notation Digraph.outNeighborSet

@[simp] theorem mem_inNeighborSet (v w : V) : v ∈ G.inNeighborSet w ↔ Adj G v w := Iff.rfl
@[simp] theorem mem_outNeighborSet (v w : V) : v ∈ G.outNeighborSet w ↔ Adj G w v := Iff.rfl

instance inNeighborSet.memDecidable (v : V) [DecidableRel (Adj G)] :
    DecidablePred (· ∈ G.inNeighborSet v) := show DecidablePred (Adj G · v) from inferInstance

instance outNeighborSet.memDecidable (v : V) [DecidableRel (Adj G)] :
    DecidablePred (· ∈ G.outNeighborSet v) := show DecidablePred (Adj G v ·) from inferInstance

@[simp] theorem inNeighborSet_inv : G.inv.inNeighborSet = G.outNeighborSet := rfl
@[simp] theorem outNeighborSet_inv : G.inv.outNeighborSet = G.inNeighborSet := rfl

end InAndOutSupport

/-! ## Map and comap -/

/-- Given a function, there is an covariant induced map on graphs by pushing forward
the adjacency relation. Whenever two adjacent vertices map to the same vertex, then
that vertex is self-adjacent in the image.

This is injective when `f` is injective (see `Digraph.map_injective`). -/
protected def map (f : V → W) (G : Digraph V) : Digraph W := ⟨Relation.Map (Adj G) f f⟩

@[simp]
theorem map_adj (f : V → W) (G : Digraph V) (u v : W) :
    Adj (G.map f) u v ↔ ∃ u' v' : V, Adj G u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

theorem map_monotone (f : V → W) : Monotone (Digraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  refine ⟨u, v, h ha, rfl, rfl⟩

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `Digraph.induce` for a wrapper.

This is surjective when `f` is injective (see `Digraph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : Digraph V where
  Adj u v := Adj G (f u) (f v)

theorem comap_monotone (f : V → W) : Monotone (Digraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : Digraph V) : (G.map f).comap f = G := by
  ext
  simp

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (Digraph.comap f) (Digraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (Digraph.map f) :=
  (leftInverse_comap_map f).injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (Digraph.comap f) :=
  (leftInverse_comap_map f).surjective

theorem map_le_iff_le_comap (f : V → W) (G : Digraph V) (G' : Digraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V → W) (G : Digraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `Digraph V` and `Digraph s`.

TODO: There is also a notion of induced subgraphs (see `Digraph.subgraph.induce`). -/

/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `Digraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : Digraph V) : Digraph s := G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `Digraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `Digraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : Digraph s) : Digraph V := G.map (Function.Embedding.subtype _)

theorem induce_spanningCoe {s : Set V} {G : Digraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanningCoe_induce_le (G : Digraph V) (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _

section VertexFiniteness

variable (G : Digraph V)

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote these conditions by
`Fintype (G.inNeighborSet v)` and `Fintype (G.outNeighborSet v)`.

We define `G.inNeighborFinset v` and `G.outNeighborFinset v` to be `Finset` versions of
`G.inNeighborSet v` and `G.outNeighborSet v`.
-/

/-- `G.inNeighborFinset v` is the `Finset` version of `G.inNeighborSet v` in case `G` is
locally finite at `v`. -/
def inNeighborFinset (v : V) [Fintype (G.inNeighborSet v)] : Finset V :=
  (G.inNeighborSet v).toFinset

/-- `G.outNeighborFinset v` is the `Finset` version of `G.outNeighborSet v` in case `G` is
locally finite at `v`. -/
def outNeighborFinset (v : V) [Fintype (G.outNeighborSet v)] : Finset V :=
  (G.outNeighborSet v).toFinset

-- pp_extended_field_notation Digraph.inNeighborFinset
-- pp_extended_field_notation Digraph.outNeighborFinset

@[simp]
theorem mem_inNeighborFinset (v w : V) [Fintype (G.inNeighborSet v)] :
    w ∈ G.inNeighborFinset v ↔ Adj G w v := Set.mem_toFinset

@[simp]
theorem mem_outNeighborFinset (v w : V) [Fintype (G.outNeighborSet v)] :
    w ∈ G.outNeighborFinset v ↔ Adj G v w := Set.mem_toFinset

@[simp] theorem inNeighborFinSet_inv : G.inv.inNeighborFinset = G.outNeighborFinset := rfl
@[simp] theorem outNeighborFinSet_inv : G.inv.outNeighborFinset = G.inNeighborFinset := rfl

/-- `G.inDegree v` is the number of vertices adjacent *to* `v`. -/
def inDegree (v : V) [Fintype (G.inNeighborSet v)] : ℕ := (G.inNeighborFinset v).card

/-- `G.outDegree v` is the number of vertices `v` is adjacent *to*. -/
def outDegree (v : V) [Fintype (G.outNeighborSet v)] : ℕ := (G.outNeighborFinset v).card

-- pp_extended_field_notation Digraph.inDegree
-- pp_extended_field_notation Digraph.outDegree

@[simp]
theorem card_inNeighborFinset_eq_inDegree (v : V) [Fintype (G.inNeighborSet v)] :
  (G.inNeighborFinset v).card = G.inDegree v := rfl

@[simp]
theorem card_outNeighborFinset_eq_outDegree (v : V) [Fintype (G.outNeighborSet v)] :
  (G.outNeighborFinset v).card = G.outDegree v := rfl

@[simp]
theorem card_inNeighborSet_eq_inDegree (v : V) [Fintype (G.inNeighborSet v)] :
    Fintype.card (G.inNeighborSet v) = G.inDegree v :=
  (Set.toFinset_card _).symm

@[simp]
theorem card_outNeighborSet_eq_outDegree (v : V) [Fintype (G.outNeighborSet v)] :
    Fintype.card (G.outNeighborSet v) = G.outDegree v :=
  (Set.toFinset_card _).symm

@[simp] theorem inDegree_inv : G.inv.inDegree = G.outDegree := rfl
@[simp] theorem outDegree_inv : G.inv.outDegree = G.inDegree := rfl

theorem inDegree_pos_iff_exists_adj (v : V) [Fintype (G.inNeighborSet v)] :
    0 < G.inDegree v ↔ ∃ w, Adj G w v := by
  simp only [inDegree, Finset.card_pos, Finset.Nonempty, mem_inNeighborFinset]

theorem outDegree_pos_iff_exists_adj (v : V) [Fintype (G.outNeighborSet v)] :
    0 < G.outDegree v ↔ ∃ w, Adj G v w := by
  simp only [outDegree, Finset.card_pos, Finset.Nonempty, mem_outNeighborFinset]

section Finite

variable [Fintype V]

instance inNeighborSetFintype [DecidableRel (Adj G)] (v : V) : Fintype (G.inNeighborSet v) :=
  Subtype.fintype _

instance outNeighborSetFintype [DecidableRel (Adj G)] (v : V) : Fintype (G.outNeighborSet v) :=
  Subtype.fintype _

theorem inNeighborFinset_eq_filter {v : V} [DecidableRel (Adj G)] :
    G.inNeighborFinset v = Finset.univ.filter (Adj G · v) := by ext; simp

theorem outNeighborFinset_eq_filter {v : V} [DecidableRel (Adj G)] :
    G.outNeighborFinset v = Finset.univ.filter (Adj G v ·) := by ext; simp

@[simp]
theorem inDegree_top (v : V) : (⊤ : Digraph V).inDegree v = Fintype.card V := by
  erw [inDegree, inNeighborFinset_eq_filter, Finset.filter_True]
  rfl

@[simp]
theorem outDegree_top (v : V) : (⊤ : Digraph V).outDegree v = Fintype.card V := inDegree_top v

@[simp]
theorem inDegree_bot (v : V) : (⊥ : Digraph V).inDegree v = 0 := by
  erw [inDegree, inNeighborFinset_eq_filter, Finset.filter_False]
  rfl

@[simp]
theorem outDegree_bot (v : V) : (⊥ : Digraph V).outDegree v = 0 := inDegree_bot v

theorem inDegree_le_card_verts [DecidableRel (Adj G)] (v : V) : G.inDegree v ≤ Fintype.card V :=
  Finset.card_le_card (Finset.subset_univ _)

theorem outDegree_le_card_verts [DecidableRel (Adj G)] (v : V) : G.outDegree v ≤ Fintype.card V :=
  Finset.card_le_card (Finset.subset_univ _)

end Finite

end VertexFiniteness

section Maps

/-! ### Graph homomorphisms

We get graph homomorphisms from the `HasAdj` class. Here we give properties
specialized to `Digraph`.
-/

namespace Hom

variable {G : Digraph V} {G' : Digraph W} (f : G →g G')

theorem apply_mem_inNeighborSet {v w : V} (h : w ∈ G.inNeighborSet v) :
    f w ∈ G'.inNeighborSet (f v) := Hom.map_adj f h

theorem apply_mem_outNeighborSet {v w : V} (h : w ∈ G.outNeighborSet v) :
    f w ∈ G'.outNeighborSet (f v) := Hom.map_adj f h

/-- The map between in-neighbor sets induced by a homomorphism. -/
@[simps]
def mapInNeighborSet (v : V) (w : G.inNeighborSet v) : G'.inNeighborSet (f v) :=
  ⟨f w, apply_mem_inNeighborSet f w.property⟩

/-- The map between out-neighbor sets induced by a homomorphism. -/
@[simps]
def mapOutNeighborSet (v : V) (w : G.outNeighborSet v) : G'.outNeighborSet (f v) :=
  ⟨f w, apply_mem_outNeighborSet f w.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : Digraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

variable {G''}

end Hom

namespace Embedding

variable {G : Digraph V} {G' : Digraph W} (f : G ↪g G')

theorem apply_mem_inNeighborSet_iff {v w : V} :
    f w ∈ G'.inNeighborSet (f v) ↔ w ∈ G.inNeighborSet v :=
  Embedding.map_adj_iff f

theorem apply_mem_outNeighborSet_iff {v w : V} :
    f w ∈ G'.outNeighborSet (f v) ↔ w ∈ G.outNeighborSet v :=
  Embedding.map_adj_iff f

/-- A graph embedding induces an embedding of in-neighbor sets. -/
@[simps]
def mapInNeighborSet (v : V) : G.inNeighborSet v ↪ G'.inNeighborSet (f v) where
  toFun w := ⟨f w, (apply_mem_inNeighborSet_iff f).mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

/-- A graph embedding induces an embedding of out-neighbor sets. -/
@[simps]
def mapOutNeighborSet (v : V) : G.outNeighborSet v ↪ G'.outNeighborSet (f v) where
  toFun w := ⟨f w, (apply_mem_outNeighborSet_iff f).mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
protected def comap (f : V ↪ W) (G : Digraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem comap_apply (f : V ↪ W) (G : Digraph W) (v : V) : Digraph.Embedding.comap f G v = f v := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
protected def map (f : V ↪ W) (G : Digraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem map_apply (f : V ↪ W) (G : Digraph V) (v : V) :
  Digraph.Embedding.map f G v = f v := rfl

/-- Induced graphs embed in the original graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  Digraph.Embedding.comap (Function.Embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : Digraph s) : G ↪g G.spanningCoe :=
  Digraph.Embedding.map (Function.Embedding.subtype _) G

end Embedding

section InduceHom

variable {G : Digraph V} {G' : Digraph W} {G'' : Digraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def InduceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

@[simp, norm_cast] lemma coe_induceHom : InduceHom φ φst = Set.MapsTo.restrict φ s t φst := rfl

@[simp] lemma induceHom_id (G : Digraph V) (s) :
    InduceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl

@[simp] lemma induceHom_comp :
    (InduceHom ψ ψtr).comp (InduceHom φ φst) = InduceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl

end InduceHom

namespace Iso

variable {G : Digraph V} {G' : Digraph W} (f : G ≃g G')

theorem apply_mem_inNeighborSet_iff {v w : V} :
    f w ∈ G'.inNeighborSet (f v) ↔ w ∈ G.inNeighborSet v :=
  Iso.map_adj_iff f

theorem apply_mem_outNeighborSet_iff {v w : V} :
    f w ∈ G'.outNeighborSet (f v) ↔ w ∈ G.outNeighborSet v :=
  Iso.map_adj_iff f

/-- A graph isomorphism induces an equivalence of in-neighbor sets. -/
@[simps]
def mapInNeighborSet (v : V) : G.inNeighborSet v ≃ G'.inNeighborSet (f v) where
  toFun w := ⟨f w, (apply_mem_inNeighborSet_iff f).mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using (apply_mem_inNeighborSet_iff f.symm).mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

/-- A graph isomorphism induces an equivalence of out-neighbor sets. -/
@[simps]
def mapOutNeighborSet (v : V) : G.outNeighborSet v ≃ G'.outNeighborSet (f v) where
  toFun w := ⟨f w, (apply_mem_outNeighborSet_iff f).mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using (apply_mem_outNeighborSet_iff f.symm).mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
protected def comap (f : V ≃ W) (G : Digraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma comap_apply (f : V ≃ W) (G : Digraph W) (v : V) :
  Digraph.Iso.comap f G v = f v := rfl

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : Digraph W) (w : W) :
  (Digraph.Iso.comap f G).symm w = f.symm w := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
protected def map (f : V ≃ W) (G : Digraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma map_apply (f : V ≃ W) (G : Digraph V) (v : V) :
  Digraph.Iso.map f G v = f v := rfl

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : Digraph V) (w : W) :
  (Digraph.Iso.map f G).symm w = f.symm w := rfl

end Iso

end Maps

end Digraph
