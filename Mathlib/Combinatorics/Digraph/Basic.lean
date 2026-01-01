/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
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

open Finset Function

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
  /-- Every vertex in an edge is contained in `verts` -/
  edge_verts : ∀ v w : V, Adj v w → v ∈ verts ∧ w ∈ verts

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
-/
@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨{v | ∃ w, x v w == true ∨ x w v = true},fun v w ↦ x v w,
    by
      simp only [beq_true, Set.mem_setOf_eq]
      intro v w xvw
      exact ⟨⟨w, by tauto⟩, ⟨v, by tauto⟩⟩⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro ⟨_, h⟩
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)


-- instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
--   Fintype.ofBijective Digraph.mk' <| by
--     classical
--     refine ⟨Embedding.injective _, ?_⟩
--     intro G
--     use fun v w ↦ G.Adj v w
--     -- ext v w
--     -- · simp
--     --   constructor
--     --   · rintro ⟨w, (h | h)⟩
--     --     · exact (G.edge_verts v w h).1
--     --     · exact (G.edge_verts w v h).2
--     --   ·
--     --     done
--     -- · sorry


namespace Digraph

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where
  verts := ⊤
  Adj := ⊤
  edge_verts := by
    intro v w h
    tauto

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges.
-/
protected def emptyDigraph (V : Type*) : Digraph V where
  Adj _ _ := False
  verts := ∅
  edge_verts := by
    intro v w a
    simp_all only

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  verts := Set.univ
  edge_verts := by
    intros
    simp only [Set.mem_univ, and_self]

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

-- Note : `adj_injective is no longer true
-- theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) :=
--  fun G₁ G₂ ↦ Digraph.ext


@[simp] theorem adj_inj {G H : Digraph V} : verts G = verts H ∧ G.Adj = H.Adj  ↔ G = H :=
  Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a spanning subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (Digraph V) where
  max x y := {
    verts := x.verts ⊔ y.verts
    Adj := x.Adj ⊔ y.Adj
    edge_verts := by
      intro v w maxAdj
      constructor
      all_goals
        simp_all only [Pi.sup_apply, sup_Prop_eq, Set.sup_eq_union, Set.mem_union]
        obtain (xAdj | yAdj) := maxAdj
        · apply x.edge_verts at xAdj
          tauto
        · apply y.edge_verts at yAdj
          tauto
  }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (Digraph V) where
  min x y := {
    verts := x.verts ⊓ y.verts
    Adj := x.Adj ⊓ y.Adj
    edge_verts := by
      intro v w minAdj
      simp_all only [Pi.inf_apply, inf_Prop_eq, Set.inf_eq_inter, Set.mem_inter_iff]
      obtain ⟨xAdj, yAdj⟩ := minAdj
      apply x.edge_verts at xAdj
      apply y.edge_verts at yAdj
      tauto
    }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance hasCompl : HasCompl (Digraph V) where
  compl G := {
    verts := G.verts
    Adj := fun v w ↦ v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w
    edge_verts := by
      intros; tauto
  }
@[simp] theorem compl_adj (G : Digraph V) (v w : V) (hmem : v ∈ G.verts ∧ w ∈ G.verts)
  : Gᶜ.Adj v w ↔ ¬G.Adj v w := by
  constructor
  · intro compl_adj
    simp[hasCompl] at compl_adj
    tauto
  · intro adj
    simp [hasCompl]
    tauto

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := {
    verts := x.verts
    Adj := x.Adj \ y.Adj
    edge_verts := by
      intro v w sdiff_adj
      apply x.edge_verts
      exact sdiff_adj.left
  }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s := {
      verts := {v | ∃ G ∈ s, v ∈ G.verts}
      Adj := fun a b ↦ ∃ G ∈ s, Adj G a b
      edge_verts := by
        intro v w ⟨G, G_in_s, G_Adj⟩
        simp only [Set.mem_setOf_eq]
        constructor
        all_goals
          use G
          constructor <;> try exact G_in_s
        · exact (G.edge_verts v w G_Adj).left
        · exact (G.edge_verts v w G_Adj).right
      }

instance infSet : InfSet (Digraph V) where
  sInf s := {
    verts := {v | ∀ G ∈ s, v ∈ G.verts}
    Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b)
    edge_verts := by
      intro v w hG
      simp only [Set.mem_setOf_eq]
      constructor
      all_goals
        intro G G_in_s
        specialize hG G_in_s
      · exact (G.edge_verts v w hG).left
      · exact (G.edge_verts v w hG).right
  }


@[simp]
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { adj_injective.distribLattice Digraph.Adj (fun _ _ ↦ rfl) fun _ _ ↦ rfl with
    le := fun G H ↦ ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) where
  top := Digraph.completeDigraph V
  bot := Digraph.emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  inf_compl_le_bot G v w h := absurd h.2.2.2 (by simp [h.1])
  top_le_sup_compl G v w h := by
    sorry
  le_sSup _ G hG _ _ hab := ⟨G, hG, hab⟩
  sSup_le s G hG a b := by
    rintro ⟨H, hH, hab⟩
    exact hG _ hH hab
  sInf_le _ _ hG _ _ hab := hab hG
  le_sInf _ _ hG _ _ hab _ hH := hG _ hH hab
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl

@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl

@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
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

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

end Digraph
