/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2

#align_import combinatorics.simple_graph.basic from "leanprover-community/mathlib"@"c6ef6387ede9983aee397d442974e61f89dfd87b"

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `SimpleGraph` is a structure for symmetric, irreflexive relations

* `SimpleGraph.neighborSet` is the `Set` of vertices adjacent to a given vertex

* `SimpleGraph.commonNeighbors` is the intersection of the neighbor sets of two given vertices

* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
   if `neighborSet` is finite

* `SimpleGraph.incidenceSet` is the `Set` of edges containing a given vertex

* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
   if `incidenceSet` is finite

* `SimpleGraph.Dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

* `SimpleGraph.Hom`, `SimpleGraph.Embedding`, and `SimpleGraph.Iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `SimpleGraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.

* Given instances `DecidableRel G.Adj` and `Fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding`, and `RelIso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`.

## Todo

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/

-- porting note: using `aesop` for automation

-- porting note: These attributes are needed to use `aesop` as a replacement for `obviously`
attribute [aesop norm unfold (rule_sets [SimpleGraph])] Symmetric
attribute [aesop norm unfold (rule_sets [SimpleGraph])] Irreflexive

-- porting note: a thin wrapper around `aesop` for graph lemmas, modelled on `aesop_cat`
/--
A variant of the `aesop` tactic for use in the graph library. Changes relative
to standard `aesop`:

- We use the `SimpleGraph` rule set in addition to the default rule sets.
- We instruct Aesop's `intro` rule to unfold with `default` transparency.
- We instruct Aesop to fail if it can't fully solve the goal. This allows us to
  use `aesop_graph` for auto-params.
-/
macro (name := aesop_graph) "aesop_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, terminal := true })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

/--
Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`
-/
macro (name := aesop_graph?) "aesop_graph?" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, terminal := true })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

/--
A variant of `aesop_graph` which does not fail if it is unable to solve the
goal. Use this only for exploration! Nonterminal Aesop is even worse than
nonterminal `simp`.
-/
macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, warnOnNonterminal := false })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

open Finset Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets [SimpleGraph])]
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph
#align simple_graph SimpleGraph
-- porting note: changed `obviously` to `aesop` in the `structure`

noncomputable instance {V : Type u} [Fintype V] : Fintype (SimpleGraph V) := by
  classical exact Fintype.ofInjective SimpleGraph.Adj SimpleGraph.ext
  -- 🎉 no goals

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V
    where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
  symm := fun _ _ ⟨hn, hr⟩ => ⟨hn.symm, hr.symm⟩
  loopless := fun _ ⟨hn, _⟩ => hn rfl
#align simple_graph.from_rel SimpleGraph.fromRel

@[simp]
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl
#align simple_graph.from_rel_adj SimpleGraph.fromRel_adj

-- porting note: attributes needed for `completeGraph`
attribute [aesop safe (rule_sets [SimpleGraph])] Ne.symm
attribute [aesop safe (rule_sets [SimpleGraph])] Ne.irrefl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def completeGraph (V : Type u) : SimpleGraph V where Adj := Ne
#align complete_graph completeGraph

/-- The graph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def emptyGraph (V : Type u) : SimpleGraph V where Adj _ _ := False
#align empty_graph emptyGraph

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
def completeBipartiteGraph (V W : Type*) : SimpleGraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm v w := by cases v <;> cases w <;> simp
                 -- ⊢ (fun v w => Sum.isLeft v = true ∧ Sum.isRight w = true ∨ Sum.isRight v = tru …
                             -- ⊢ (fun v w => Sum.isLeft v = true ∧ Sum.isRight w = true ∨ Sum.isRight v = tru …
                             -- ⊢ (fun v w => Sum.isLeft v = true ∧ Sum.isRight w = true ∨ Sum.isRight v = tru …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
  loopless v := by cases v <;> simp
                   -- ⊢ ¬(fun v w => Sum.isLeft v = true ∧ Sum.isRight w = true ∨ Sum.isRight v = tr …
                               -- 🎉 no goals
                               -- 🎉 no goals
#align complete_bipartite_graph completeBipartiteGraph

namespace SimpleGraph

variable {ι : Sort*} {𝕜 : Type*} {V : Type u} {W : Type v} {X : Type w} (G : SimpleGraph V)
  (G' : SimpleGraph W) {a b c u v w : V} {e : Sym2 V}

@[simp]
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless v
#align simple_graph.irrefl SimpleGraph.irrefl

theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  ⟨fun x => G.symm x, fun x => G.symm x⟩
#align simple_graph.adj_comm SimpleGraph.adj_comm

@[symm]
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm h
#align simple_graph.adj_symm SimpleGraph.adj_symm

theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h
#align simple_graph.adj.symm SimpleGraph.Adj.symm

theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  rintro rfl
  -- ⊢ False
  exact G.irrefl h
  -- 🎉 no goals
#align simple_graph.ne_of_adj SimpleGraph.ne_of_adj

protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h
#align simple_graph.adj.ne SimpleGraph.Adj.ne

protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.ne.symm
#align simple_graph.adj.ne' SimpleGraph.Adj.ne'

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)
#align simple_graph.ne_of_adj_of_not_adj SimpleGraph.ne_of_adj_of_not_adj

theorem adj_injective : Injective (Adj : SimpleGraph V → V → V → Prop) :=
  SimpleGraph.ext
#align simple_graph.adj_injective SimpleGraph.adj_injective

@[simp]
theorem adj_inj {G H : SimpleGraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff
#align simple_graph.adj_inj SimpleGraph.adj_inj

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
#align simple_graph.is_subgraph SimpleGraph.IsSubgraph

instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : SimpleGraph V → SimpleGraph V → Prop) = (· ≤ ·) :=
  rfl
#align simple_graph.is_subgraph_eq_le SimpleGraph.isSubgraph_eq_le

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Sup (SimpleGraph V) where
  sup x y :=
    { Adj := x.Adj ⊔ y.Adj
      symm := fun v w h => by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }
                              -- 🎉 no goals

@[simp]
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl
#align simple_graph.sup_adj SimpleGraph.sup_adj

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (SimpleGraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj
      symm := fun v w h => by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }
                              -- 🎉 no goals

@[simp]
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl
#align simple_graph.inf_adj SimpleGraph.inf_adj

/-- We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance hasCompl : HasCompl (SimpleGraph V) where
  compl G :=
    { Adj := fun v w => v ≠ w ∧ ¬G.Adj v w
      symm := fun v w ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩
                                                -- 🎉 no goals
      loopless := fun v ⟨hne, _⟩ => (hne rfl).elim }

@[simp]
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w :=
  Iff.rfl
#align simple_graph.compl_adj SimpleGraph.compl_adj

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj
      symm := fun v w h => by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }
                              -- ⊢ Adj x w v ∧ ¬Adj y w v
                                                             -- 🎉 no goals

@[simp]
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl
#align simple_graph.sdiff_adj SimpleGraph.sdiff_adj

instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b
      symm := fun a b => Exists.imp $ fun _ => And.imp_right Adj.symm
      loopless := by
        rintro a ⟨G, _, ha⟩
        -- ⊢ False
        exact ha.ne rfl }
        -- 🎉 no goals

instance infSet : InfSet (SimpleGraph V) where
  sInf s :=
    { Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) ∧ a ≠ b
      symm := fun _ _ => And.imp (forall₂_imp fun _ _ => Adj.symm) Ne.symm
      loopless := fun _ h => h.2 rfl }

@[simp]
theorem sSup_adj {s : Set (SimpleGraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl
#align simple_graph.Sup_adj SimpleGraph.sSup_adj

@[simp]
theorem sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b :=
  Iff.rfl
#align simple_graph.Inf_adj SimpleGraph.sInf_adj

@[simp]
theorem iSup_adj {f : ι → SimpleGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]
                                                                                         -- 🎉 no goals
#align simple_graph.supr_adj SimpleGraph.iSup_adj

@[simp]
theorem iInf_adj {f : ι → SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]
  -- 🎉 no goals
#align simple_graph.infi_adj SimpleGraph.iInf_adj

theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      -- ⊢ (∀ (G : SimpleGraph V), G ∈ s → Adj G a b) → a ≠ b
      exact fun h => (h _ hG).ne
      -- 🎉 no goals
#align simple_graph.Inf_adj_of_nonempty SimpleGraph.sInf_adj_of_nonempty

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SimpleGraph V} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _), Set.forall_range_iff]
  -- 🎉 no goals
#align simple_graph.infi_adj_of_nonempty SimpleGraph.iInf_adj_of_nonempty

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (SimpleGraph V) :=
  { show DistribLattice (SimpleGraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SimpleGraph V) :=
  { SimpleGraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w h => x.ne_of_adj h
    bot_le := fun x v w h => h.elim
    sdiff_eq := fun x y => by
      ext v w
      -- ⊢ Adj (x \ y) v w ↔ Adj (x ⊓ yᶜ) v w
      refine' ⟨fun h => ⟨h.1, ⟨_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      -- ⊢ v ≠ w
      rintro rfl
      -- ⊢ False
      exact x.irrefl h.1
      -- ⊢ Adj (G ⊔ Gᶜ) v w
      -- ⊢ Adj (G ⊔ Gᶜ) v w
      -- 🎉 no goals
        -- 🎉 no goals
    inf_compl_le_bot := fun G v w h => False.elim <| h.2.2 h.1
        -- 🎉 no goals
      -- ⊢ Adj G a b
    top_le_sup_compl := fun G v w hvw => by
      -- 🎉 no goals
      by_cases G.Adj v w
      · exact Or.inl h
      · exact Or.inr ⟨hvw, h⟩
    sSup := sSup
                                -- ⊢ Adj (⨅ (a : ι✝), ⨆ (b : κ✝ a), f a b) x✝¹ x✝ ↔ Adj (⨆ (g : (a : ι✝) → κ✝ a), …
                                     -- 🎉 no goals
    le_sSup := fun s G hG a b hab => ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b => by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab => hab.1 hG
    le_sInf := fun s G hG a b hab => ⟨fun H hH => hG _ hH hab, hab.ne⟩
    iInf_iSup_eq := fun f => by ext; simp [Classical.skolem] }

@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
#align simple_graph.top_adj SimpleGraph.top_adj

@[simp]
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl
#align simple_graph.bot_adj SimpleGraph.bot_adj

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl
#align simple_graph.complete_graph_eq_top SimpleGraph.completeGraph_eq_top

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl
#align simple_graph.empty_graph_eq_bot SimpleGraph.emptyGraph_eq_bot

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False
#align simple_graph.bot.adj_decidable SimpleGraph.Bot.adjDecidable

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w
#align simple_graph.sup.adj_decidable SimpleGraph.Sup.adjDecidable

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w
#align simple_graph.inf.adj_decidable SimpleGraph.Inf.adjDecidable

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w
#align simple_graph.sdiff.adj_decidable SimpleGraph.Sdiff.adjDecidable

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w
#align simple_graph.top.adj_decidable SimpleGraph.Top.adjDecidable

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w ∧ ¬G.Adj v w
#align simple_graph.compl.adj_decidable SimpleGraph.Compl.adjDecidable

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V :=
  Rel.dom G.Adj
#align simple_graph.support SimpleGraph.support

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_support SimpleGraph.mem_support

theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  Rel.dom_mono h
#align simple_graph.support_mono SimpleGraph.support_mono

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def neighborSet (v : V) : Set V := {w | G.Adj v w}
#align simple_graph.neighbor_set SimpleGraph.neighborSet

instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)
#align simple_graph.neighbor_set.mem_decidable SimpleGraph.neighborSet.memDecidable

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h ⟦(a, b)⟧, fun h e => Sym2.ind @h e⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

#align simple_graph.edge_set SimpleGraph.edgeSetEmbedding

@[simp]
theorem mem_edgeSet : ⟦(v, w)⟧ ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_edge_set SimpleGraph.mem_edgeSet

theorem not_isDiag_of_mem_edgeSet : e ∈ edgeSet G → ¬e.IsDiag :=
  Sym2.ind (fun _ _ => Adj.ne) e
#align simple_graph.not_is_diag_of_mem_edge_set SimpleGraph.not_isDiag_of_mem_edgeSet

theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq
#align simple_graph.edge_set_inj SimpleGraph.edgeSet_inj

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ :=
  (edgeSetEmbedding V).le_iff_le
#align simple_graph.edge_set_subset_edge_set SimpleGraph.edgeSet_subset_edgeSet

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ :=
  (edgeSetEmbedding V).lt_iff_lt
#align simple_graph.edge_set_ssubset_edge_set SimpleGraph.edgeSet_ssubset_edgeSet

theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  (edgeSetEmbedding V).injective
#align simple_graph.edge_set_injective SimpleGraph.edgeSet_injective

alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet
#align simple_graph.edge_set_mono SimpleGraph.edgeSet_mono

alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet
#align simple_graph.edge_set_strict_mono SimpleGraph.edgeSet_strict_mono

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot
#align simple_graph.edge_set_bot SimpleGraph.edgeSet_bot

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  -- ⊢ Quot.mk Setoid.r (x, y) ∈ edgeSet (G₁ ⊔ G₂) ↔ Quot.mk Setoid.r (x, y) ∈ edge …
  rfl
  -- 🎉 no goals
#align simple_graph.edge_set_sup SimpleGraph.edgeSet_sup

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  -- ⊢ Quot.mk Setoid.r (x, y) ∈ edgeSet (G₁ ⊓ G₂) ↔ Quot.mk Setoid.r (x, y) ∈ edge …
  rfl
  -- 🎉 no goals
#align simple_graph.edge_set_inf SimpleGraph.edgeSet_inf

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  -- ⊢ Quot.mk Setoid.r (x, y) ∈ edgeSet (G₁ \ G₂) ↔ Quot.mk Setoid.r (x, y) ∈ edge …
  rfl
  -- 🎉 no goals
#align simple_graph.edge_set_sdiff SimpleGraph.edgeSet_sdiff

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_from_edgeSet`,
allows proving `(G \ from_edgeSet s).edge_set = G.edgeSet \ s` by `simp`. -/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ { e | e.IsDiag }) = G.edgeSet \ s := by
  ext e
  -- ⊢ e ∈ edgeSet G \ (s \ {e | Sym2.IsDiag e}) ↔ e ∈ edgeSet G \ s
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not, and_congr_right_iff]
  -- ⊢ e ∈ edgeSet G → (e ∈ s → Sym2.IsDiag e ↔ ¬e ∈ s)
  intro h
  -- ⊢ e ∈ s → Sym2.IsDiag e ↔ ¬e ∈ s
  simp only [G.not_isDiag_of_mem_edgeSet h, imp_false]
  -- 🎉 no goals
#align simple_graph.edge_set_sdiff_sdiff_is_diag SimpleGraph.edgeSet_sdiff_sdiff_isDiag

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine' ⟨fun _ => ⟨G.ne_of_adj ‹_›, ⟦(v, w)⟧, by simpa⟩, _⟩
  -- ⊢ (v ≠ w ∧ ∃ e, e ∈ edgeSet G ∧ v ∈ e ∧ w ∈ e) → Adj G v w
  rintro ⟨hne, e, he, hv⟩
  -- ⊢ Adj G v w
  rw [Sym2.mem_and_mem_iff hne] at hv
  -- ⊢ Adj G v w
  subst e
  -- ⊢ Adj G v w
  rwa [mem_edgeSet] at he
  -- 🎉 no goals
#align simple_graph.adj_iff_exists_edge SimpleGraph.adj_iff_exists_edge

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = ⟦(a, b)⟧ := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]
  -- 🎉 no goals
#align simple_graph.adj_iff_exists_edge_coe SimpleGraph.adj_iff_exists_edge_coe

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  erw [← Sym2.other_spec h, Sym2.eq_swap] at he
  -- ⊢ Sym2.Mem.other h ≠ v
  exact G.ne_of_adj he
  -- 🎉 no goals
#align simple_graph.edge_other_ne SimpleGraph.edge_other_ne

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm
#align simple_graph.decidable_mem_edge_set SimpleGraph.decidableMemEdgeSet

instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _
#align simple_graph.fintype_edge_set SimpleGraph.fintypeEdgeSet

instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  -- ⊢ Fintype ↑∅
  infer_instance
  -- 🎉 no goals
#align simple_graph.fintype_edge_set_bot SimpleGraph.fintypeEdgeSetBot

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  -- ⊢ Fintype ↑(edgeSet G₁ ∪ edgeSet G₂)
  infer_instance
  -- 🎉 no goals
#align simple_graph.fintype_edge_set_sup SimpleGraph.fintypeEdgeSetSup

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  -- ⊢ Fintype ↑(edgeSet G₁ ∩ edgeSet G₂)
  exact Set.fintypeInter _ _
  -- 🎉 no goals
#align simple_graph.fintype_edge_set_inf SimpleGraph.fintypeEdgeSetInf

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  -- ⊢ Fintype ↑(edgeSet G₁ \ edgeSet G₂)
  exact Set.fintypeDiff _ _
  -- 🎉 no goals
#align simple_graph.fintype_edge_set_sdiff SimpleGraph.fintypeEdgeSetSdiff

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/-- `fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops. -/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm v w h := ⟨Sym2.toRel_symmetric s h.1, h.2.symm⟩
#align simple_graph.from_edge_set SimpleGraph.fromEdgeSet

@[simp]
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ ⟦(v, w)⟧ ∈ s ∧ v ≠ w :=
  Iff.rfl
#align simple_graph.from_edge_set_adj SimpleGraph.fromEdgeSet_adj

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `⟦(u, v)⟧ ∈ (fromEdgeSet s).edgeSet` ==> `⟦(v, w)⟧ ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } := by
  ext e
  -- ⊢ e ∈ edgeSet (fromEdgeSet s) ↔ e ∈ s \ {e | Sym2.IsDiag e}
  exact Sym2.ind (by simp) e
  -- 🎉 no goals
#align simple_graph.edge_set_from_edge_set SimpleGraph.edgeSet_fromEdgeSet

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext v w
  -- ⊢ Adj (fromEdgeSet (edgeSet G)) v w ↔ Adj G v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩
  -- 🎉 no goals
#align simple_graph.from_edge_set_edge_set SimpleGraph.fromEdgeSet_edgeSet

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext v w
  -- ⊢ Adj (fromEdgeSet ∅) v w ↔ Adj ⊥ v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and_iff, bot_adj]
  -- 🎉 no goals
#align simple_graph.from_edge_set_empty SimpleGraph.fromEdgeSet_empty

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext v w
  -- ⊢ Adj (fromEdgeSet Set.univ) v w ↔ Adj ⊤ v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and_iff, top_adj]
  -- 🎉 no goals
#align simple_graph.from_edge_set_univ SimpleGraph.fromEdgeSet_univ

@[simp]
theorem fromEdgeSet_inf (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊓ fromEdgeSet t = fromEdgeSet (s ∩ t) := by
  ext v w
  -- ⊢ Adj (fromEdgeSet s ⊓ fromEdgeSet t) v w ↔ Adj (fromEdgeSet (s ∩ t)) v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne.def, inf_adj]
  -- ⊢ (Quotient.mk (Sym2.Rel.setoid V) (v, w) ∈ s ∧ ¬v = w) ∧ Quotient.mk (Sym2.Re …
  tauto
  -- 🎉 no goals
#align simple_graph.from_edge_set_inf SimpleGraph.fromEdgeSet_inf

@[simp]
theorem fromEdgeSet_sup (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊔ fromEdgeSet t = fromEdgeSet (s ∪ t) := by
  ext v w
  -- ⊢ Adj (fromEdgeSet s ⊔ fromEdgeSet t) v w ↔ Adj (fromEdgeSet (s ∪ t)) v w
  simp [Set.mem_union, or_and_right]
  -- 🎉 no goals
#align simple_graph.from_edge_set_sup SimpleGraph.fromEdgeSet_sup

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet s \ fromEdgeSet t = fromEdgeSet (s \ t) := by
  ext v w
  -- ⊢ Adj (fromEdgeSet s \ fromEdgeSet t) v w ↔ Adj (fromEdgeSet (s \ t)) v w
  constructor <;> simp (config := { contextual := true })
  -- ⊢ Adj (fromEdgeSet s \ fromEdgeSet t) v w → Adj (fromEdgeSet (s \ t)) v w
                  -- 🎉 no goals
                  -- 🎉 no goals
#align simple_graph.from_edge_set_sdiff SimpleGraph.fromEdgeSet_sdiff

@[mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  rintro v w
  -- ⊢ Adj (fromEdgeSet s) v w → Adj (fromEdgeSet t) v w
  simp (config := { contextual := true }) only [fromEdgeSet_adj, Ne.def, not_false_iff,
    and_true_iff, and_imp]
  exact fun vws _ => h vws
  -- 🎉 no goals
#align simple_graph.from_edge_set_mono SimpleGraph.fromEdgeSet_mono

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  -- ⊢ Fintype ↑(s \ {e | Sym2.IsDiag e})
  infer_instance
  -- 🎉 no goals

end FromEdgeSet

/-! ## Darts -/

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart extends V × V where
  is_adj : G.Adj fst snd
  deriving DecidableEq
#align simple_graph.dart SimpleGraph.Dart

initialize_simps_projections Dart (+toProd, -fst, -snd)

section Darts

variable {G}

theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp
  -- ⊢ { toProd := toProd✝, is_adj := is_adj✝ } = d₂ ↔ { toProd := toProd✝, is_adj  …
            -- ⊢ { toProd := toProd✝¹, is_adj := is_adj✝¹ } = { toProd := toProd✝, is_adj :=  …
                      -- 🎉 no goals
#align simple_graph.dart.ext_iff SimpleGraph.Dart.ext_iff

@[ext]
theorem Dart.ext (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h
#align simple_graph.dart.ext SimpleGraph.Dart.ext

-- Porting note: deleted `Dart.fst` and `Dart.snd` since they are now invalid declaration names,
-- even though there is not actually a `SimpleGraph.Dart.fst` or `SimpleGraph.Dart.snd`.

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  Dart.ext
#align simple_graph.dart.to_prod_injective SimpleGraph.Dart.toProd_injective

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩
      left_inv := fun s => by ext <;> simp
                              -- ⊢ ((fun d => { fst := d.fst, snd := { val := d.snd, property := (_ : Adj G d.f …
                                      -- 🎉 no goals
                                      -- 🎉 no goals
      right_inv := fun d => by ext <;> simp }
                               -- ⊢ ((fun s => { toProd := (s.fst, ↑s.snd), is_adj := (_ : ↑s.snd ∈ neighborSet  …
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align simple_graph.dart.fintype SimpleGraph.Dart.fintype

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  ⟦d.toProd⟧
#align simple_graph.dart.edge SimpleGraph.Dart.edge

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = ⟦p⟧ :=
  rfl
#align simple_graph.dart.edge_mk SimpleGraph.Dart.edge_mk

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.edgeSet :=
  d.is_adj
#align simple_graph.dart.edge_mem SimpleGraph.Dart.edge_mem

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, G.symm d.is_adj⟩
#align simple_graph.dart.symm SimpleGraph.Dart.symm

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl
#align simple_graph.dart.symm_mk SimpleGraph.Dart.symm_mk

@[simp]
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.mk''_prod_swap_eq
#align simple_graph.dart.edge_symm SimpleGraph.Dart.edge_symm

@[simp]
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm
#align simple_graph.dart.edge_comp_symm SimpleGraph.Dart.edge_comp_symm

@[simp]
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _
#align simple_graph.dart.symm_symm SimpleGraph.Dart.symm_symm

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  Dart.symm_symm
#align simple_graph.dart.symm_involutive SimpleGraph.Dart.symm_involutive

theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.is_adj.ne
#align simple_graph.dart.symm_ne SimpleGraph.Dart.symm_ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  -- ⊢ Dart.edge { toProd := p, is_adj := hp } = Dart.edge { toProd := q, is_adj := …
  simp [Sym2.mk''_eq_mk''_iff, -Quotient.eq]
  -- 🎉 no goals
#align simple_graph.dart_edge_eq_iff SimpleGraph.dart_edge_eq_iff

theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {p : V × V}, d.edge = ⟦p⟧ ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  -- ⊢ ∀ {p_1 : V × V}, Dart.edge { toProd := p, is_adj := h } = Quotient.mk (Sym2. …
  apply Sym2.mk''_eq_mk''_iff
  -- 🎉 no goals
#align simple_graph.dart_edge_eq_mk_iff SimpleGraph.dart_edge_eq_mk'_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V},
      d.edge = ⟦(u, v)⟧ ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  -- ⊢ Dart.edge { toProd := (a, b), is_adj := h } = Quotient.mk (Sym2.Rel.setoid V …
  rw [dart_edge_eq_mk'_iff]
  -- ⊢ { toProd := (a, b), is_adj := h }.toProd = (u, v) ∨ { toProd := (a, b), is_a …
  simp
  -- 🎉 no goals
#align simple_graph.dart_edge_eq_mk_iff' SimpleGraph.dart_edge_eq_mk'_iff'

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst
#align simple_graph.dart_adj SimpleGraph.DartAdj

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩
#align simple_graph.dart_of_neighbor_set SimpleGraph.dartOfNeighborSet

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    -- ⊢ ↑e₁ = ↑e₂
    convert congr_arg Prod.snd h'
    -- 🎉 no goals
#align simple_graph.dart_of_neighbor_set_injective SimpleGraph.dartOfNeighborSet_injective

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  -- ⊢ Nonempty (Dart ⊤)
  exact ⟨⟨(v, w), h⟩⟩
  -- 🎉 no goals
#align simple_graph.nonempty_dart_top SimpleGraph.nonempty_dart_top

end Darts

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
#align simple_graph.incidence_set SimpleGraph.incidenceSet

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1
#align simple_graph.incidence_set_subset SimpleGraph.incidenceSet_subset

theorem mk'_mem_incidenceSet_iff : ⟦(b, c)⟧ ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff
#align simple_graph.mk_mem_incidence_set_iff SimpleGraph.mk'_mem_incidenceSet_iff

theorem mk'_mem_incidenceSet_left_iff : ⟦(a, b)⟧ ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk''_left _ _
#align simple_graph.mk_mem_incidence_set_left_iff SimpleGraph.mk'_mem_incidenceSet_left_iff

theorem mk'_mem_incidenceSet_right_iff : ⟦(a, b)⟧ ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk''_right _ _
#align simple_graph.mk_mem_incidence_set_right_iff SimpleGraph.mk'_mem_incidenceSet_right_iff

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2
#align simple_graph.edge_mem_incidence_set_iff SimpleGraph.edge_mem_incidenceSet_iff

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {⟦(a, b)⟧} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩
#align simple_graph.incidence_set_inter_incidence_set_subset SimpleGraph.incidenceSet_inter_incidenceSet_subset

theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {⟦(a, b)⟧} := by
  refine' (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm _
  -- ⊢ {Quotient.mk (Sym2.Rel.setoid V) (a, b)} ⊆ incidenceSet G a ∩ incidenceSet G b
  rintro _ (rfl : _ = ⟦(a, b)⟧)
  -- ⊢ Quotient.mk (Sym2.Rel.setoid V) (a, b) ∈ incidenceSet G a ∩ incidenceSet G b
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩
  -- 🎉 no goals
#align simple_graph.incidence_set_inter_incidence_set_of_adj SimpleGraph.incidenceSet_inter_incidenceSet_of_adj

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]
#align simple_graph.adj_of_mem_incidence_set SimpleGraph.adj_of_mem_incidenceSet

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and]
  -- ⊢ ∀ (x : Sym2 V), x ∈ incidenceSet G a → ¬x ∈ incidenceSet G b
  intro u ha hb
  -- ⊢ False
  exact h (G.adj_of_mem_incidenceSet hn ha hb)
  -- 🎉 no goals
#align simple_graph.incidence_set_inter_incidence_set_of_not_adj SimpleGraph.incidenceSet_inter_incidenceSet_of_not_adj

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G.edgeSet ∧ v ∈ e
#align simple_graph.decidable_mem_incidence_set SimpleGraph.decidableMemIncidenceSet

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
@[reducible]
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
#align simple_graph.edge_finset SimpleGraph.edgeFinset

@[norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _
#align simple_graph.coe_edge_finset SimpleGraph.coe_edgeFinset

variable {G}

theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset
#align simple_graph.mem_edge_finset SimpleGraph.mem_edgeFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1
#align simple_graph.not_is_diag_of_mem_edge_finset SimpleGraph.not_isDiag_of_mem_edgeFinset

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp
                                                                       -- 🎉 no goals
#align simple_graph.edge_finset_inj SimpleGraph.edgeFinset_inj

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp
                                                                                     -- 🎉 no goals
#align simple_graph.edge_finset_subset_edge_finset SimpleGraph.edgeFinset_subset_edgeFinset

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp
                                                                                      -- 🎉 no goals
#align simple_graph.edge_finset_ssubset_edge_finset SimpleGraph.edgeFinset_ssubset_edgeFinset

alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset
#align simple_graph.edge_finset_mono SimpleGraph.edgeFinset_mono

alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset
#align simple_graph.edge_finset_strict_mono SimpleGraph.edgeFinset_strict_mono

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]
                                                                  -- 🎉 no goals
#align simple_graph.edge_finset_bot SimpleGraph.edgeFinset_bot

@[simp]
theorem edgeFinset_sup [DecidableEq V] : (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by
  simp [edgeFinset]
  -- 🎉 no goals
#align simple_graph.edge_finset_sup SimpleGraph.edgeFinset_sup

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]
  -- 🎉 no goals
#align simple_graph.edge_finset_inf SimpleGraph.edgeFinset_inf

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] : (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset :=
  by simp [edgeFinset]
     -- 🎉 no goals
#align simple_graph.edge_finset_sdiff SimpleGraph.edgeFinset_sdiff

theorem edgeFinset_card : G.edgeFinset.card = Fintype.card G.edgeSet :=
  Set.toFinset_card _
#align simple_graph.edge_finset_card SimpleGraph.edgeFinset_card

@[simp]
theorem edgeSet_univ_card : (univ : Finset G.edgeSet).card = G.edgeFinset.card :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset
#align simple_graph.edge_set_univ_card SimpleGraph.edgeSet_univ_card

end EdgeFinset

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_neighbor_set SimpleGraph.mem_neighborSet

@[simp]
theorem mem_incidenceSet (v w : V) : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]
  -- 🎉 no goals
#align simple_graph.mem_incidence_set SimpleGraph.mem_incidenceSet

theorem mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v :=
  by simp only [mem_incidenceSet, mem_neighborSet]
     -- 🎉 no goals
#align simple_graph.mem_incidence_iff_neighbor SimpleGraph.mem_incidence_iff_neighbor

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  -- ⊢ e' ∈ incidenceSet G v ∩ incidenceSet G (Sym2.Mem.other h) ↔ e' ∈ {e}
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  -- ⊢ (e' ∈ edgeSet G ∧ v ∈ e') ∧ e' ∈ edgeSet G ∧ Sym2.Mem.other h ∈ e' ↔ e' = e
  refine' ⟨fun h' => _, _⟩
  -- ⊢ e' = e
  · rw [← Sym2.other_spec h]
    -- ⊢ e' = Quotient.mk (Sym2.Rel.setoid V) (v, Sym2.Mem.other h)
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ (e' ∈ edgeSet G ∧ v ∈ e') ∧ e' ∈ edgeSet G ∧ Sym2.Mem.other h ∈ e'
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩
    -- 🎉 no goals
#align simple_graph.adj_incidence_set_inter SimpleGraph.adj_incidenceSet_inter

theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  -- ⊢ neighborSet G v ∩ neighborSet Gᶜ v ⊆ ∅
  rintro w ⟨h, h'⟩
  -- ⊢ w ∈ ∅
  rw [mem_neighborSet, compl_adj] at h'
  -- ⊢ w ∈ ∅
  exact h'.2 h
  -- 🎉 no goals
#align simple_graph.compl_neighbor_set_disjoint SimpleGraph.compl_neighborSet_disjoint

theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ := by
  ext w
  -- ⊢ w ∈ neighborSet G v ∪ neighborSet Gᶜ v ↔ w ∈ {v}ᶜ
  have h := @ne_of_adj _ G
  -- ⊢ w ∈ neighborSet G v ∪ neighborSet Gᶜ v ↔ w ∈ {v}ᶜ
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  -- ⊢ Adj G v w ∨ v ≠ w ∧ ¬Adj G v w ↔ ¬w = v
  tauto
  -- 🎉 no goals
#align simple_graph.neighbor_set_union_compl_neighbor_set_eq SimpleGraph.neighborSet_union_compl_neighborSet_eq

theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v ∪ Gᶜ.neighborSet v : Set V)] :
    (Set.toFinset (G.neighborSet v ∪ Gᶜ.neighborSet v)).card = Fintype.card V - 1 := by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]
#align simple_graph.card_neighbor_set_union_compl_neighbor_set SimpleGraph.card_neighborSet_union_compl_neighborSet

theorem neighborSet_compl (G : SimpleGraph V) (v : V) :
    Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v} := by
  ext w
  -- ⊢ w ∈ neighborSet Gᶜ v ↔ w ∈ (neighborSet G v)ᶜ \ {v}
  simp [and_comm, eq_comm]
  -- 🎉 no goals
#align simple_graph.neighbor_set_compl SimpleGraph.neighborSet_compl

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w
#align simple_graph.common_neighbors SimpleGraph.commonNeighbors

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl
#align simple_graph.common_neighbors_eq SimpleGraph.commonNeighbors_eq

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl
#align simple_graph.mem_common_neighbors SimpleGraph.mem_commonNeighbors

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _
#align simple_graph.common_neighbors_symm SimpleGraph.commonNeighbors_symm

theorem not_mem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl
#align simple_graph.not_mem_common_neighbors_left SimpleGraph.not_mem_commonNeighbors_left

theorem not_mem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl
#align simple_graph.not_mem_common_neighbors_right SimpleGraph.not_mem_commonNeighbors_right

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left _ _
#align simple_graph.common_neighbors_subset_neighbor_set_left SimpleGraph.commonNeighbors_subset_neighborSet_left

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right _ _
#align simple_graph.common_neighbors_subset_neighbor_set_right SimpleGraph.commonNeighbors_subset_neighborSet_right

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) :=
  inferInstanceAs <| DecidablePred fun u => u ∈ G.neighborSet v ∧ u ∈ G.neighborSet w
#align simple_graph.decidable_mem_common_neighbors SimpleGraph.decidableMemCommonNeighbors

theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext u
  -- ⊢ u ∈ commonNeighbors ⊤ v w ↔ u ∈ Set.univ \ {v, w}
  simp [commonNeighbors, eq_comm, not_or]
  -- 🎉 no goals
#align simple_graph.common_neighbors_top_eq SimpleGraph.commonNeighbors_top_eq

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2
#align simple_graph.other_vertex_of_incident SimpleGraph.otherVertexOfIncident

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  -- ⊢ otherVertexOfIncident G h ∈ e
  simp [otherVertexOfIncident, Sym2.other_mem']
  -- 🎉 no goals
#align simple_graph.edge_other_incident_set SimpleGraph.edge_other_incident_set

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  cases' h with he hv
  -- ⊢ otherVertexOfIncident G (_ : e ∈ edgeSet G ∧ v ∈ e) ∈ neighborSet G v
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he
  -- 🎉 no goals
#align simple_graph.incidence_other_prop SimpleGraph.incidence_other_prop

-- Porting note: as a simp lemma this does not apply even to itself
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)
#align simple_graph.incidence_other_neighbor_edge SimpleGraph.incidence_other_neighbor_edge

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v
    where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
                   -- 🎉 no goals
  right_inv := fun ⟨w, hw⟩ => by
    simp only [mem_neighborSet, Subtype.mk.injEq]
    -- ⊢ otherVertexOfIncident G (_ : ↑((fun w => { val := Quotient.mk (Sym2.Rel.seto …
    exact incidence_other_neighbor_edge _ hw
    -- 🎉 no goals
#align simple_graph.incidence_set_equiv_neighbor_set SimpleGraph.incidenceSetEquivNeighborSet

end Incidence

/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V
    where
  Adj := G.Adj \ Sym2.ToRel s
  symm a b := by simp [adj_comm, Sym2.eq_swap]
                 -- 🎉 no goals
  loopless a := by simp [SDiff.sdiff] -- porting note: used to be handled by `obviously`
                   -- 🎉 no goals
#align simple_graph.delete_edges SimpleGraph.deleteEdges

@[simp]
theorem deleteEdges_adj (s : Set (Sym2 V)) (v w : V) :
    (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬⟦(v, w)⟧ ∈ s :=
  Iff.rfl
#align simple_graph.delete_edges_adj SimpleGraph.deleteEdges_adj

theorem sdiff_eq_deleteEdges (G G' : SimpleGraph V) : G \ G' = G.deleteEdges G'.edgeSet := by
  ext
  -- ⊢ Adj (G \ G') x✝¹ x✝ ↔ Adj (deleteEdges G (edgeSet G')) x✝¹ x✝
  simp
  -- 🎉 no goals
#align simple_graph.sdiff_eq_delete_edges SimpleGraph.sdiff_eq_deleteEdges

theorem deleteEdges_eq_sdiff_fromEdgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G \ fromEdgeSet s := by
  ext
  -- ⊢ Adj (deleteEdges G s) x✝¹ x✝ ↔ Adj (G \ fromEdgeSet s) x✝¹ x✝
  exact ⟨fun h => ⟨h.1, not_and_of_not_left _ h.2⟩, fun h => ⟨h.1, not_and'.mp h.2 h.ne⟩⟩
  -- 🎉 no goals
#align simple_graph.delete_edges_eq_sdiff_from_edge_set SimpleGraph.deleteEdges_eq_sdiff_fromEdgeSet

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : SimpleGraph V).deleteEdges G.edgeSet := by
  ext
  -- ⊢ Adj Gᶜ x✝¹ x✝ ↔ Adj (deleteEdges ⊤ (edgeSet G)) x✝¹ x✝
  simp
  -- 🎉 no goals
#align simple_graph.compl_eq_delete_edges SimpleGraph.compl_eq_deleteEdges

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by
  ext
  -- ⊢ Adj (deleteEdges (deleteEdges G s) s') x✝¹ x✝ ↔ Adj (deleteEdges G (s ∪ s')) …
  simp [and_assoc, not_or]
  -- 🎉 no goals
#align simple_graph.delete_edges_delete_edges SimpleGraph.deleteEdges_deleteEdges

@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  -- ⊢ Adj (deleteEdges G ∅) x✝¹ x✝ ↔ Adj G x✝¹ x✝
  simp
  -- 🎉 no goals
#align simple_graph.delete_edges_empty_eq SimpleGraph.deleteEdges_empty_eq

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ := by
  ext
  -- ⊢ Adj (deleteEdges G Set.univ) x✝¹ x✝ ↔ Adj ⊥ x✝¹ x✝
  simp
  -- 🎉 no goals
#align simple_graph.delete_edges_univ_eq SimpleGraph.deleteEdges_univ_eq

theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro
  -- ⊢ ∀ ⦃w : V⦄, Adj (deleteEdges G s) v✝ w → Adj G v✝ w
  simp (config := { contextual := true })
  -- 🎉 no goals
#align simple_graph.delete_edges_le SimpleGraph.deleteEdges_le

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [deleteEdges_adj, and_imp, true_and_iff]
  -- ⊢ Adj G v w → ¬Quotient.mk (Sym2.Rel.setoid V) (v, w) ∈ s' → ¬Quotient.mk (Sym …
  exact fun _ hn hs => hn (h hs)
  -- 🎉 no goals
#align simple_graph.delete_edges_le_of_le SimpleGraph.deleteEdges_le_of_le

theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  -- ⊢ Adj (deleteEdges G s) x✝¹ x✝ ↔ Adj (deleteEdges G (s ∩ edgeSet G)) x✝¹ x✝
  simp (config := { contextual := true }) [imp_false]
  -- 🎉 no goals
#align simple_graph.delete_edges_eq_inter_edge_set SimpleGraph.deleteEdges_eq_inter_edgeSet

theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext v w
  -- ⊢ Adj (deleteEdges G (edgeSet G \ edgeSet H)) v w ↔ Adj H v w
  constructor <;> simp (config := { contextual := true }) [@h v w]
  -- ⊢ Adj (deleteEdges G (edgeSet G \ edgeSet H)) v w → Adj H v w
                  -- 🎉 no goals
                  -- 🎉 no goals
#align simple_graph.delete_edges_sdiff_eq_of_le SimpleGraph.deleteEdges_sdiff_eq_of_le

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e
  -- ⊢ e ∈ edgeSet (deleteEdges G s) ↔ e ∈ edgeSet G \ s
  refine' Sym2.ind _ e
  -- ⊢ ∀ (x y : V), Quotient.mk (Sym2.Rel.setoid V) (x, y) ∈ edgeSet (deleteEdges G …
  simp
  -- 🎉 no goals
#align simple_graph.edge_set_delete_edges SimpleGraph.edgeSet_deleteEdges

-- porting note: added `Fintype (Sym2 V)` argument rather than have it be inferred.
-- As a consequence, deleted the `Fintype V` argument.
theorem edgeFinset_deleteEdges [Fintype (Sym2 V)] [DecidableEq V] [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) [DecidableRel (G.deleteEdges s).Adj] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  -- ⊢ e ∈ edgeFinset (deleteEdges G ↑s) ↔ e ∈ edgeFinset G \ s
  simp [edgeSet_deleteEdges]
  -- 🎉 no goals
#align simple_graph.edge_finset_delete_edges SimpleGraph.edgeFinset_deleteEdges

section DeleteFar

-- porting note: added `Fintype (Sym2 V)` argument.
variable [OrderedRing 𝕜] [Fintype V] [Fintype (Sym2 V)] [DecidableEq V] [DecidableRel G.Adj]
  {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ s.card
#align simple_graph.delete_far SimpleGraph.DeleteFar

open Classical

variable {G}

theorem deleteFar_iff :
    G.DeleteFar p r ↔ ∀ ⦃H⦄, H ≤ G → p H → r ≤ G.edgeFinset.card - H.edgeFinset.card := by
  refine' ⟨fun h H hHG hH => _, fun h s hs hG => _⟩
  -- ⊢ r ≤ ↑(card (edgeFinset G)) - ↑(card (edgeFinset H))
  · have := h (sdiff_subset G.edgeFinset H.edgeFinset)
    -- ⊢ r ≤ ↑(card (edgeFinset G)) - ↑(card (edgeFinset H))
    simp only [deleteEdges_sdiff_eq_of_le _ hHG, edgeFinset_mono hHG, card_sdiff,
      card_le_of_subset, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
    -- 🎉 no goals
  · simpa [card_sdiff hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_of_subset hs] using h (G.deleteEdges_le s) hG
#align simple_graph.delete_far_iff SimpleGraph.deleteFar_iff

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff
#align simple_graph.delete_far.le_card_sub_card SimpleGraph.DeleteFar.le_card_sub_card

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG
#align simple_graph.delete_far.mono SimpleGraph.DeleteFar.mono

end DeleteFar

/-! ## Map and comap -/


/-- Given an injective function, there is a covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `SimpleGraph.map_injective`). -/
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Relation.Map G.Adj f f
  symm a b := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, rfl⟩
    -- ⊢ Relation.Map G.Adj (↑f) (↑f) (↑f w) (↑f v)
    use w, v, h.symm, rfl
    -- 🎉 no goals
  loopless a := by -- porting note: `obviously` used to handle this
    rintro ⟨v, w, h, rfl, h'⟩
    -- ⊢ False
    exact h.ne (f.injective h'.symm)
    -- 🎉 no goals
#align simple_graph.map SimpleGraph.map

@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl
#align simple_graph.map_adj SimpleGraph.map_adj

theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  -- ⊢ Adj (SimpleGraph.map f G') (↑f u) (↑f v)
  exact ⟨_, _, h ha, rfl, rfl⟩
  -- 🎉 no goals
#align simple_graph.map_monotone SimpleGraph.map_monotone

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm _ _ h := h.symm
  loopless _ := G.loopless _
#align simple_graph.comap SimpleGraph.comap

theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) := by
  intro G G' h _ _ ha
  -- ⊢ Adj (SimpleGraph.comap (↑f) G') v✝ w✝
  exact h ha
  -- 🎉 no goals
#align simple_graph.comap_monotone SimpleGraph.comap_monotone

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  -- ⊢ Adj (SimpleGraph.comap (↑f) (SimpleGraph.map f G)) x✝¹ x✝ ↔ Adj G x✝¹ x✝
  simp
  -- 🎉 no goals
#align simple_graph.comap_map_eq SimpleGraph.comap_map_eq

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f
#align simple_graph.left_inverse_comap_map SimpleGraph.leftInverse_comap_map

theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective
#align simple_graph.map_injective SimpleGraph.map_injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective
#align simple_graph.comap_surjective SimpleGraph.comap_surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    -- ⊢ Adj G' (↑f u) (↑f v)
    exact h ha⟩
    -- 🎉 no goals
#align simple_graph.map_le_iff_le_comap SimpleGraph.map_le_iff_le_comap

theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]
  -- 🎉 no goals
#align simple_graph.map_comap_le SimpleGraph.map_comap_le

lemma le_comap_of_subsingleton (f : V → W) [Subsingleton V] : G ≤ G'.comap f := by
  intros v w; simp [Subsingleton.elim v w]
  -- ⊢ Adj G v w → Adj (SimpleGraph.comap f G') v w
              -- 🎉 no goals

lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f ≤ G' := by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton
  -- ⊢ G ≤ SimpleGraph.comap (↑f) G'
                            -- 🎉 no goals

/-- Given a family of vertex types indexed by `ι`, pulling back from `⊤ : SimpleGraph ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal. -/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst ⊤

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `SimpleGraph V` and `SimpleGraph s`.

There is also a notion of induced subgraphs (see `SimpleGraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
#align simple_graph.induce SimpleGraph.induce

@[simp] lemma induce_singleton_eq_top (v : V) : G.induce {v} = ⊤ := by
  rw [eq_top_iff]; apply le_comap_of_subsingleton
  -- ⊢ ⊤ ≤ induce {v} G
                   -- 🎉 no goals

/-- Given a graph on a set of vertices, we can make it be a `SimpleGraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `SimpleGraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)
#align simple_graph.spanning_coe SimpleGraph.spanningCoe

theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _
#align simple_graph.induce_spanning_coe SimpleGraph.induce_spanningCoe

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _
#align simple_graph.spanning_coe_induce_le SimpleGraph.spanningCoe_induce_le

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

/-- `G.neighbors v` is the `Finset` version of `G.Adj v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
#align simple_graph.neighbor_finset SimpleGraph.neighborFinset

theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl
#align simple_graph.neighbor_finset_def SimpleGraph.neighborFinset_def

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset
#align simple_graph.mem_neighbor_finset SimpleGraph.mem_neighborFinset

theorem not_mem_neighborFinset_self : v ∉ G.neighborFinset v := by simp
                                                                   -- 🎉 no goals
#align simple_graph.not_mem_neighbor_finset_self SimpleGraph.not_mem_neighborFinset_self

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| not_mem_neighborFinset_self _ _
#align simple_graph.neighbor_finset_disjoint_singleton SimpleGraph.neighborFinset_disjoint_singleton

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| not_mem_neighborFinset_self _ _
#align simple_graph.singleton_disjoint_neighbor_finset SimpleGraph.singleton_disjoint_neighborFinset

/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ :=
  (G.neighborFinset v).card
#align simple_graph.degree SimpleGraph.degree

-- Porting note: in Lean 3 we could do `simp [← degree]`, but that gives
-- "invalid '←' modifier, 'SimpleGraph.degree' is a declaration name to be unfolded".
-- In any case, having this lemma is good since there's no guarantee we won't still change
-- the definition of `degree`.
@[simp]
theorem card_neighborFinset_eq_degree : (G.neighborFinset v).card = G.degree v := rfl

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm
#align simple_graph.card_neighbor_set_eq_degree SimpleGraph.card_neighborSet_eq_degree

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]
  -- 🎉 no goals
#align simple_graph.degree_pos_iff_exists_adj SimpleGraph.degree_pos_iff_exists_adj

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_disjoint_union (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]
#align simple_graph.degree_compl SimpleGraph.degree_compl

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm
#align simple_graph.incidence_set_fintype SimpleGraph.incidenceSetFintype

/-- This is the `Finset` version of `incidenceSet`. -/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset
#align simple_graph.incidence_finset SimpleGraph.incidenceFinset

@[simp]
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]
  -- ⊢ Fintype.card ↑(neighborSet G v) = degree G v
  simp
  -- 🎉 no goals
#align simple_graph.card_incidence_set_eq_degree SimpleGraph.card_incidenceSet_eq_degree

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] :
    (G.incidenceFinset v).card = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  -- ⊢ card (incidenceFinset G v) = Fintype.card ↑(incidenceSet G v)
  apply Set.toFinset_card
  -- 🎉 no goals
#align simple_graph.card_incidence_finset_eq_degree SimpleGraph.card_incidenceFinset_eq_degree

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset
#align simple_graph.mem_incidence_finset SimpleGraph.mem_incidenceFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = G.edgeFinset.filter (Membership.mem v) := by
  ext e
  -- ⊢ e ∈ incidenceFinset G v ↔ e ∈ filter (Membership.mem v) (edgeFinset G)
  refine' Sym2.ind (fun x y => _) e
  -- ⊢ Quotient.mk (Sym2.Rel.setoid V) (x, y) ∈ incidenceFinset G v ↔ Quotient.mk ( …
  simp [mk'_mem_incidenceSet_iff]
  -- 🎉 no goals
#align simple_graph.incidence_finset_eq_filter SimpleGraph.incidenceFinset_eq_filter

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
@[reducible]
def LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)
#align simple_graph.locally_finite SimpleGraph.LocallyFinite

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d
#align simple_graph.is_regular_of_degree SimpleGraph.IsRegularOfDegree

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v
#align simple_graph.is_regular_of_degree.degree_eq SimpleGraph.IsRegularOfDegree.degree_eq

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  -- ⊢ degree Gᶜ v = Fintype.card V - 1 - k
  rw [degree_compl, h v]
  -- 🎉 no goals
#align simple_graph.is_regular_of_degree.compl SimpleGraph.IsRegularOfDegree.compl

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ _
    (by
      simp_rw [mem_neighborSet]
      -- ⊢ DecidablePred fun x => Adj G v x
      infer_instance)
      -- 🎉 no goals
    _
#align simple_graph.neighbor_set_fintype SimpleGraph.neighborSetFintype

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = Finset.univ.filter (G.Adj v) := by
  ext
  -- ⊢ a✝ ∈ neighborFinset G v ↔ a✝ ∈ filter (Adj G v) univ
  simp
  -- 🎉 no goals
#align simple_graph.neighbor_finset_eq_filter SimpleGraph.neighborFinset_eq_filter

theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]
#align simple_graph.neighbor_finset_compl SimpleGraph.neighborFinset_compl

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  erw [degree, neighborFinset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]
  -- 🎉 no goals
#align simple_graph.complete_graph_degree SimpleGraph.complete_graph_degree

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  erw [degree, neighborFinset_eq_filter, filter_False]
  -- ⊢ card ∅ = 0
  exact Finset.card_empty
  -- 🎉 no goals
#align simple_graph.bot_degree SimpleGraph.bot_degree

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  -- ⊢ degree ⊤ v = Fintype.card V - 1
  simp
  -- 🎉 no goals
#align simple_graph.is_regular_of_degree.top SimpleGraph.IsRegularOfDegree.top

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untop' 0 (univ.image fun v => G.degree v).min
#align simple_graph.min_degree SimpleGraph.minDegree

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  -- ⊢ ∃ v, minDegree G = degree G v
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  -- ⊢ ∃ v, minDegree G = degree G v
  refine' ⟨v, by simp [minDegree, ht]⟩
  -- 🎉 no goals
#align simple_graph.exists_minimal_degree_vertex SimpleGraph.exists_minimal_degree_vertex

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  -- ⊢ minDegree G ≤ degree G v
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  -- ⊢ minDegree G ≤ degree G v
  rwa [minDegree, ht]
  -- 🎉 no goals
#align simple_graph.min_degree_le_degree SimpleGraph.minDegree_le_degree

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  -- ⊢ k ≤ minDegree G
  rw [hv]
  -- ⊢ k ≤ degree G v
  apply h
  -- 🎉 no goals
#align simple_graph.le_min_degree_of_forall_le_degree SimpleGraph.le_minDegree_of_forall_le_degree

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  Option.getD (univ.image fun v => G.degree v).max 0
#align simple_graph.max_degree SimpleGraph.maxDegree

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  -- ⊢ ∃ v, maxDegree G = degree G v
  have ht₂ := mem_of_max ht
  -- ⊢ ∃ v, maxDegree G = degree G v
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  -- ⊢ ∃ v, maxDegree G = degree G v
  rcases ht₂ with ⟨v, _, rfl⟩
  -- ⊢ ∃ v, maxDegree G = degree G v
  refine' ⟨v, _⟩
  -- ⊢ maxDegree G = degree G v
  rw [maxDegree, ht]
  -- ⊢ Option.getD (↑(degree G v)) 0 = degree G v
  rfl
  -- 🎉 no goals
#align simple_graph.exists_maximal_degree_vertex SimpleGraph.exists_maximal_degree_vertex

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  -- ⊢ degree G v ≤ maxDegree G
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  -- ⊢ degree G v ≤ maxDegree G
  rwa [maxDegree, ht]
  -- 🎉 no goals
#align simple_graph.degree_le_max_degree SimpleGraph.degree_le_maxDegree

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  -- ⊢ maxDegree G ≤ k
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    -- ⊢ maxDegree G ≤ k
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    -- ⊢ maxDegree G ≤ k
    rw [hv]
    -- ⊢ degree G v ≤ k
    apply h
    -- 🎉 no goals
  · rw [not_nonempty_iff_eq_empty] at hV
    -- ⊢ maxDegree G ≤ k
    rw [maxDegree, hV, image_empty]
    -- ⊢ Option.getD (Finset.max ∅) 0 ≤ k
    exact zero_le k
    -- 🎉 no goals
#align simple_graph.max_degree_le_of_forall_degree_le SimpleGraph.maxDegree_le_of_forall_degree_le

theorem degree_lt_card_verts [DecidableRel G.Adj] (v : V) : G.degree v < Fintype.card V := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  exact ⟨v, by simp, Finset.subset_univ _⟩
#align simple_graph.degree_lt_card_verts SimpleGraph.degree_lt_card_verts

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero. -/
theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  cases' G.exists_maximal_degree_vertex with v hv
  -- ⊢ maxDegree G < Fintype.card V
  rw [hv]
  -- ⊢ degree G v < Fintype.card V
  apply G.degree_lt_card_verts v
  -- 🎉 no goals
#align simple_graph.max_degree_lt_card_verts SimpleGraph.maxDegree_lt_card_verts

theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  -- ⊢ Fintype.card ↑(commonNeighbors G v w) ≤ Fintype.card ↑(neighborSet G v)
  exact Set.card_le_of_subset (Set.inter_subset_left _ _)
  -- 🎉 no goals
#align simple_graph.card_common_neighbors_le_degree_left SimpleGraph.card_commonNeighbors_le_degree_left

theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]
  -- 🎉 no goals
#align simple_graph.card_common_neighbors_le_degree_right SimpleGraph.card_commonNeighbors_le_degree_right

theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)
#align simple_graph.card_common_neighbors_lt_card_verts SimpleGraph.card_commonNeighbors_lt_card_verts

/-- If the condition `G.Adj v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general. -/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  erw [← Set.toFinset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Finset.insert_subset_iff]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _
  · rw [Set.mem_toFinset]
    apply not_mem_commonNeighbors_right
#align simple_graph.adj.card_common_neighbors_lt_degree SimpleGraph.Adj.card_commonNeighbors_lt_degree

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  -- ⊢ card (Set.toFinset Set.univ \ Set.toFinset {v, w}) = Fintype.card V - 2
  rw [Finset.card_sdiff]
  -- ⊢ card (Set.toFinset Set.univ) - card (Set.toFinset {v, w}) = Fintype.card V - 2
  · simp [Finset.card_univ, h]
    -- 🎉 no goals
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]
    -- 🎉 no goals
#align simple_graph.card_common_neighbors_top SimpleGraph.card_commonNeighbors_top

end Finite

section Maps

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
#align simple_graph.hom SimpleGraph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
#align simple_graph.embedding SimpleGraph.Embedding

/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj
#align simple_graph.iso SimpleGraph.Iso

-- mathport name: «expr →g »
infixl:50 " →g " => Hom

-- mathport name: «expr ↪g »
infixl:50 " ↪g " => Embedding

-- mathport name: «expr ≃g »
infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbrev id : G →g G :=
  RelHom.id _
#align simple_graph.hom.id SimpleGraph.Hom.id

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
#align simple_graph.hom.map_adj SimpleGraph.Hom.map_adj

theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h
#align simple_graph.hom.map_mem_edge_set SimpleGraph.Hom.map_mem_edgeSet

theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h
#align simple_graph.hom.apply_mem_neighbor_set SimpleGraph.Hom.apply_mem_neighborSet

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩
#align simple_graph.hom.map_edge_set SimpleGraph.Hom.mapEdgeSet

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩
#align simple_graph.hom.map_neighbor_set SimpleGraph.Hom.mapNeighborSet

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩
#align simple_graph.hom.map_dart SimpleGraph.Hom.mapDart

@[simp]
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl
#align simple_graph.hom.map_dart_apply SimpleGraph.Hom.mapDart_apply

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha
#align simple_graph.hom.map_spanning_subgraphs SimpleGraph.Hom.mapSpanningSubgraphs

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  -- ⊢ mapEdgeSet f { val := e₁, property := h₁ } = mapEdgeSet f { val := e₂, prope …
  dsimp [Hom.mapEdgeSet]
  -- ⊢ { val := Sym2.map (↑f) e₁, property := (_ : Sym2.map ↑f ↑{ val := e₁, proper …
  repeat' rw [Subtype.mk_eq_mk]
  -- ⊢ Sym2.map (↑f) e₁ = Sym2.map (↑f) e₂ → e₁ = e₂
  apply Sym2.map.injective hinj
  -- 🎉 no goals
#align simple_graph.hom.map_edge_set.injective SimpleGraph.Hom.mapEdgeSet.injective

/-- Every graph homomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  -- ⊢ v = w
  contrapose! h
  -- ⊢ ↑f v ≠ ↑f w
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))
  -- 🎉 no goals
#align simple_graph.hom.injective_of_top_hom SimpleGraph.Hom.injective_of_top_hom

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp
                 -- 🎉 no goals
#align simple_graph.hom.comap SimpleGraph.Hom.comap

variable {G'' : SimpleGraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f
#align simple_graph.hom.comp SimpleGraph.Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.hom.coe_comp SimpleGraph.Hom.coe_comp

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _
#align simple_graph.embedding.refl SimpleGraph.Embedding.refl

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom
#align simple_graph.embedding.to_hom SimpleGraph.Embedding.toHom

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.embedding.map_adj_iff SimpleGraph.Embedding.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
#align simple_graph.embedding.map_mem_edge_set_iff SimpleGraph.Embedding.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.embedding.apply_mem_neighbor_set_iff SimpleGraph.Embedding.apply_mem_neighborSet_iff

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.injective
#align simple_graph.embedding.map_edge_set SimpleGraph.Embedding.mapEdgeSet

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    -- ⊢ { val := w₁, property := h₁ } = { val := w₂, property := h₂ }
    rw [Subtype.mk_eq_mk] at h ⊢
    -- ⊢ w₁ = w₂
    exact f.inj' h
    -- 🎉 no goals
#align simple_graph.embedding.map_neighbor_set SimpleGraph.Embedding.mapNeighborSet

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.embedding.comap SimpleGraph.Embedding.comap

@[simp]
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
  SimpleGraph.Embedding.comap f G v = f v := rfl
#align simple_graph.embedding.comap_apply SimpleGraph.Embedding.comap_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.embedding.map SimpleGraph.Embedding.map

@[simp]
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
  SimpleGraph.Embedding.map f G v = f v := rfl
#align simple_graph.embedding.map_apply SimpleGraph.Embedding.map_apply

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G
#align simple_graph.embedding.induce SimpleGraph.Embedding.induce

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G
#align simple_graph.embedding.spanning_coe SimpleGraph.Embedding.spanningCoe

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ↪ β) :
    (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.embedding.complete_graph SimpleGraph.Embedding.completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'
#align simple_graph.embedding.comp SimpleGraph.Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.embedding.coe_comp SimpleGraph.Embedding.coe_comp

end Embedding

section induceHom

variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def induceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'
#align simple_graph.induce_hom SimpleGraph.induceHom

@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl
#align simple_graph.coe_induce_hom SimpleGraph.coe_induceHom

@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    induceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  -- ⊢ ↑(↑(induceHom Hom.id (_ : Set.MapsTo id s s)) x) = ↑(↑Hom.id x)
  rfl
  -- 🎉 no goals
#align simple_graph.induce_hom_id SimpleGraph.induceHom_id

@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  -- ⊢ ↑(↑(Hom.comp (induceHom ψ ψtr) (induceHom φ φst)) x) = ↑(↑(induceHom (Hom.co …
  rfl
  -- 🎉 no goals
#align simple_graph.induce_hom_comp SimpleGraph.induceHom_comp

lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  erw [Set.MapsTo.restrict_inj] <;> assumption
  -- ⊢ Set.InjOn (↑φ) s
                                    -- 🎉 no goals
                                    -- 🎉 no goals

end induceHom

section induceHomLE
variable {s s' : Set V} (h : s ≤ s')

/-- Given an inclusion of vertex subsets, the induced embedding on induced graphs.
This is not an abbreviation for `induceHom` since we get an embedding in this case. -/
def induceHomOfLE (h : s ≤ s') : G.induce s ↪g G.induce s' where
  toEmbedding := Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp
                     -- 🎉 no goals

@[simp] lemma induceHomOfLE_apply (v : s) : (G.induceHomOfLE h) v = Set.inclusion h v := rfl

@[simp] lemma induceHomOfLE_toHom :
    (G.induceHomOfLE h).toHom = induceHom (.id : G →g G) ((Set.mapsTo_id s).mono_right h) := by
  ext; simp
  -- ⊢ ↑(↑(Embedding.toHom (induceHomOfLE G h)) x✝) = ↑(↑(induceHom Hom.id (_ : Set …
       -- 🎉 no goals

end induceHomLE

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _
#align simple_graph.iso.refl SimpleGraph.Iso.refl

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding
#align simple_graph.iso.to_embedding SimpleGraph.Iso.toEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom
#align simple_graph.iso.to_hom SimpleGraph.Iso.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  RelIso.symm f
#align simple_graph.iso.symm SimpleGraph.Iso.symm

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.iso.map_adj_iff SimpleGraph.Iso.map_adj_iff

theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
#align simple_graph.iso.map_mem_edge_set_iff SimpleGraph.Iso.map_mem_edgeSet_iff

theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
#align simple_graph.iso.apply_mem_neighbor_set_iff SimpleGraph.Iso.apply_mem_neighborSet_iff

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet
    where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    -- ⊢ Hom.mapEdgeSet (RelEmbedding.toRelHom (RelIso.toRelEmbedding (symm f))) (Hom …
    simp [Hom.mapEdgeSet, Sym2.map_map, RelEmbedding.toRelHom]
    -- ⊢ Sym2.map (fun x => ↑{ toFun := ↑(symm f), map_rel' := (_ : ∀ {a b : W}, Adj  …
    convert congr_fun Sym2.map_id e
    -- ⊢ ↑{ toFun := ↑(symm f), map_rel' := (_ : ∀ {a b : W}, Adj G' a b → Adj G (↑(s …
    exact RelIso.symm_apply_apply _ _
    -- 🎉 no goals
  right_inv := by
    rintro ⟨e, h⟩
    -- ⊢ Hom.mapEdgeSet (RelEmbedding.toRelHom (RelIso.toRelEmbedding f)) (Hom.mapEdg …
    simp [Hom.mapEdgeSet, Sym2.map_map, RelEmbedding.toRelHom]
    -- ⊢ Sym2.map (fun x => ↑{ toFun := ↑f, map_rel' := (_ : ∀ {a b : V}, Adj G a b → …
    convert congr_fun Sym2.map_id e
    -- ⊢ ↑{ toFun := ↑f, map_rel' := (_ : ∀ {a b : V}, Adj G a b → Adj G' (↑f a) (↑f  …
    exact RelIso.apply_symm_apply _ _
    -- 🎉 no goals
#align simple_graph.iso.map_edge_set SimpleGraph.Iso.mapEdgeSet

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v)
    where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
      -- 🎉 no goals
  left_inv w := by simp
                   -- 🎉 no goals
  right_inv w := by simp
                    -- 🎉 no goals
#align simple_graph.iso.map_neighbor_set SimpleGraph.Iso.mapNeighborSet

theorem card_eq_of_iso [Fintype V] [Fintype W] (f : G ≃g G') : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  -- ⊢ Fintype.card W = Fintype.card W
  -- porting note: need to help it to find the typeclass instances from the target expression
  apply @Fintype.card_congr' _ _ (_) (_) rfl
  -- 🎉 no goals
#align simple_graph.iso.card_eq_of_iso SimpleGraph.Iso.card_eq_of_iso

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.iso.comap SimpleGraph.Iso.comap

@[simp]
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) :
  SimpleGraph.Iso.comap f G v = f v := rfl
#align simple_graph.iso.comap_apply SimpleGraph.Iso.comap_apply

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
  (SimpleGraph.Iso.comap f G).symm w = f.symm w := rfl
#align simple_graph.iso.comap_symm_apply SimpleGraph.Iso.comap_symm_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.iso.map SimpleGraph.Iso.map

@[simp]
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) :
  SimpleGraph.Iso.map f G v = f v := rfl
#align simple_graph.iso.map_apply SimpleGraph.Iso.map_apply

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
  (SimpleGraph.Iso.map f G).symm w = f.symm w := rfl
#align simple_graph.iso.map_symm_apply SimpleGraph.Iso.map_symm_apply

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type*} (f : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
                              -- 🎉 no goals
#align simple_graph.iso.complete_graph SimpleGraph.Iso.completeGraph

theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl
#align simple_graph.iso.to_embedding_complete_graph SimpleGraph.Iso.toEmbedding_completeGraph

variable {G'' : SimpleGraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'
#align simple_graph.iso.comp SimpleGraph.Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.iso.coe_comp SimpleGraph.Iso.coe_comp

end Iso

end Maps

/-- The graph induced on `Set.univ` is isomorphic to the original graph. -/
@[simps!]
def induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_Adj, Embedding.coe_subtype,
                                Subtype.forall, Set.mem_univ, forall_true_left, implies_true]

end SimpleGraph
