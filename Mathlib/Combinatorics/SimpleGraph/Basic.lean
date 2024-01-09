/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.FunLike.Fintype
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Card

#align_import combinatorics.simple_graph.basic from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

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

initialize_simps_projections SimpleGraph (Adj → adj)

/-- Constructor for simple graphs using a symmetric irreflexive boolean function. -/
@[simps]
def SimpleGraph.mk' {V : Type u} :
    {adj : V → V → Bool // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ SimpleGraph V where
  toFun x := ⟨fun v w ↦ x.1 v w, fun v w ↦ by simp [x.2.1], fun v ↦ by simp [x.2.2]⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w

/-- We can enumerate simple graphs by enumerating all functions `V → V → Bool`
and filtering on whether they are symmetric and irreflexive. -/
instance {V : Type u} [Fintype V] [DecidableEq V] : Fintype (SimpleGraph V) where
  elems := Finset.univ.map SimpleGraph.mk'
  complete := by
    classical
    rintro ⟨Adj, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w ↦ Adj v w, ⟨?_, ?_⟩, ?_⟩
    · simp [hs.iff]
    · intro v; simp [hi v]
    · ext
      simp

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
  loopless v := by cases v <;> simp
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
  exact G.irrefl h
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

@[simp]
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl
#align simple_graph.sup_adj SimpleGraph.sup_adj

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (SimpleGraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj
      symm := fun v w h => by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

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

@[simp]
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl
#align simple_graph.sdiff_adj SimpleGraph.sdiff_adj

instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b
      symm := fun a b => Exists.imp fun _ => And.imp_right Adj.symm
      loopless := by
        rintro a ⟨G, _, ha⟩
        exact ha.ne rfl }

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
#align simple_graph.supr_adj SimpleGraph.iSup_adj

@[simp]
theorem iInf_adj {f : ι → SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]
#align simple_graph.infi_adj SimpleGraph.iInf_adj

theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne
#align simple_graph.Inf_adj_of_nonempty SimpleGraph.sInf_adj_of_nonempty

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SimpleGraph V} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _), Set.forall_range_iff]
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
      refine' ⟨fun h => ⟨h.1, ⟨_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rintro rfl
      exact x.irrefl h.1
    inf_compl_le_bot := fun G v w h => False.elim <| h.2.2 h.1
    top_le_sup_compl := fun G v w hvw => by
      by_cases h : G.Adj v w
      · exact Or.inl h
      · exact Or.inr ⟨hvw, h⟩
    sSup := sSup
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

instance [Subsingleton V] : Unique (SimpleGraph V) where
  default := ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]

instance [Nontrivial V] : Nontrivial (SimpleGraph V) :=
  ⟨⟨⊥, ⊤, fun h ↦ not_subsingleton V ⟨by simpa only [← adj_inj, Function.funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

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
(That is, `s(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

#align simple_graph.edge_set SimpleGraph.edgeSetEmbedding

@[simp]
theorem mem_edgeSet : s(v, w) ∈ G.edgeSet ↔ G.Adj v w :=
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
theorem edgeSet_top : (⊤ : SimpleGraph V).edgeSet = {e | ¬e.IsDiag} :=
  Sym2.fromRel_ne

@[simp]
theorem edgeSet_subset_setOf_not_isDiag : G.edgeSet ⊆ {e | ¬e.IsDiag} :=
  fun _ h => (Sym2.fromRel_irreflexive (sym := G.symm)).mp G.loopless h

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_sup SimpleGraph.edgeSet_sup

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_inf SimpleGraph.edgeSet_inf

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl
#align simple_graph.edge_set_sdiff SimpleGraph.edgeSet_sdiff

variable {G G₁ G₂}

@[simp] lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edgeSet_inf, ← edgeSet_bot, ← Set.le_iff_subset,
    OrderEmbedding.le_iff_le]
#align simple_graph.disjoint_edge_set SimpleGraph.disjoint_edgeSet

@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]
#align simple_graph.edge_set_eq_empty SimpleGraph.edgeSet_eq_empty

@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]
#align simple_graph.edge_set_nonempty SimpleGraph.edgeSet_nonempty

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_from_edgeSet`,
allows proving `(G \ from_edgeSet s).edge_set = G.edgeSet \ s` by `simp`. -/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ { e | e.IsDiag }) = G.edgeSet \ s := by
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not, and_congr_right_iff]
  intro h
  simp only [G.not_isDiag_of_mem_edgeSet h, imp_false]
#align simple_graph.edge_set_sdiff_sdiff_is_diag SimpleGraph.edgeSet_sdiff_sdiff_isDiag

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine' ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, _⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he
#align simple_graph.adj_iff_exists_edge SimpleGraph.adj_iff_exists_edge

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = s(a, b) := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]
#align simple_graph.adj_iff_exists_edge_coe SimpleGraph.adj_iff_exists_edge_coe

variable (G G₁ G₂)

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  erw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he
#align simple_graph.edge_other_ne SimpleGraph.edge_other_ne

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm
#align simple_graph.decidable_mem_edge_set SimpleGraph.decidableMemEdgeSet

instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _
#align simple_graph.fintype_edge_set SimpleGraph.fintypeEdgeSet

instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance
#align simple_graph.fintype_edge_set_bot SimpleGraph.fintypeEdgeSetBot

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance
#align simple_graph.fintype_edge_set_sup SimpleGraph.fintypeEdgeSetSup

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _
#align simple_graph.fintype_edge_set_inf SimpleGraph.fintypeEdgeSetInf

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _
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
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) ∈ s ∧ v ≠ w :=
  Iff.rfl
#align simple_graph.from_edge_set_adj SimpleGraph.fromEdgeSet_adj

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } := by
  ext e
  exact Sym2.ind (by simp) e
#align simple_graph.edge_set_from_edge_set SimpleGraph.edgeSet_fromEdgeSet

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩
#align simple_graph.from_edge_set_edge_set SimpleGraph.fromEdgeSet_edgeSet

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and_iff, bot_adj]
#align simple_graph.from_edge_set_empty SimpleGraph.fromEdgeSet_empty

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and_iff, top_adj]
#align simple_graph.from_edge_set_univ SimpleGraph.fromEdgeSet_univ

@[simp]
theorem fromEdgeSet_inf (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊓ fromEdgeSet t = fromEdgeSet (s ∩ t) := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne.def, inf_adj]
  tauto
#align simple_graph.from_edge_set_inf SimpleGraph.fromEdgeSet_inf

@[simp]
theorem fromEdgeSet_sup (s t : Set (Sym2 V)) :
    fromEdgeSet s ⊔ fromEdgeSet t = fromEdgeSet (s ∪ t) := by
  ext v w
  simp [Set.mem_union, or_and_right]
#align simple_graph.from_edge_set_sup SimpleGraph.fromEdgeSet_sup

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet s \ fromEdgeSet t = fromEdgeSet (s \ t) := by
  ext v w
  constructor <;> simp (config := { contextual := true })
#align simple_graph.from_edge_set_sdiff SimpleGraph.fromEdgeSet_sdiff

@[mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  rintro v w
  simp (config := { contextual := true }) only [fromEdgeSet_adj, Ne.def, not_false_iff,
    and_true_iff, and_imp]
  exact fun vws _ => h vws
#align simple_graph.from_edge_set_mono SimpleGraph.fromEdgeSet_mono

@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  conv_rhs => rw [← Set.diff_union_inter s {e : Sym2 V | e.IsDiag}]
  rw [← disjoint_edgeSet,  edgeSet_fromEdgeSet, Set.disjoint_union_right, and_iff_left]
  exact Set.disjoint_left.2 fun e he he' ↦ not_isDiag_of_mem_edgeSet _ he he'.2
#align simple_graph.disjoint_from_edge_set SimpleGraph.disjoint_fromEdgeSet

@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm, disjoint_fromEdgeSet, disjoint_comm]
#align simple_graph.from_edge_set_disjoint SimpleGraph.fromEdgeSet_disjoint

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

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
      right_inv := fun d => by ext <;> simp }
#align simple_graph.dart.fintype SimpleGraph.Dart.fintype

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  Sym2.mk d.toProd
#align simple_graph.dart.edge SimpleGraph.Dart.edge

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = Sym2.mk p :=
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
  Sym2.mk_prod_swap_eq
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
  simp
#align simple_graph.dart_edge_eq_iff SimpleGraph.dart_edge_eq_iff

theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {p : V × V}, d.edge = Sym2.mk p ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  apply Sym2.mk_eq_mk_iff
#align simple_graph.dart_edge_eq_mk_iff SimpleGraph.dart_edge_eq_mk'_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp
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
    convert congr_arg Prod.snd h'
#align simple_graph.dart_of_neighbor_set_injective SimpleGraph.dartOfNeighborSet_injective

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩
#align simple_graph.nonempty_dart_top SimpleGraph.nonempty_dart_top

end Darts

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
#align simple_graph.incidence_set SimpleGraph.incidenceSet

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1
#align simple_graph.incidence_set_subset SimpleGraph.incidenceSet_subset

theorem mk'_mem_incidenceSet_iff : s(b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff
#align simple_graph.mk_mem_incidence_set_iff SimpleGraph.mk'_mem_incidenceSet_iff

theorem mk'_mem_incidenceSet_left_iff : s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_left _ _
#align simple_graph.mk_mem_incidence_set_left_iff SimpleGraph.mk'_mem_incidenceSet_left_iff

theorem mk'_mem_incidenceSet_right_iff : s(a, b) ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_right _ _
#align simple_graph.mk_mem_incidence_set_right_iff SimpleGraph.mk'_mem_incidenceSet_right_iff

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2
#align simple_graph.edge_mem_incidence_set_iff SimpleGraph.edge_mem_incidenceSet_iff

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {s(a, b)} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩
#align simple_graph.incidence_set_inter_incidence_set_subset SimpleGraph.incidenceSet_inter_incidenceSet_subset

theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {s(a, b)} := by
  refine' (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm _
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩
#align simple_graph.incidence_set_inter_incidence_set_of_adj SimpleGraph.incidenceSet_inter_incidenceSet_of_adj

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]
#align simple_graph.adj_of_mem_incidence_set SimpleGraph.adj_of_mem_incidenceSet

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)
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
#align simple_graph.edge_finset_inj SimpleGraph.edgeFinset_inj

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp
#align simple_graph.edge_finset_subset_edge_finset SimpleGraph.edgeFinset_subset_edgeFinset

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp
#align simple_graph.edge_finset_ssubset_edge_finset SimpleGraph.edgeFinset_ssubset_edgeFinset

alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset
#align simple_graph.edge_finset_mono SimpleGraph.edgeFinset_mono

alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset
#align simple_graph.edge_finset_strict_mono SimpleGraph.edgeFinset_strict_mono

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]
#align simple_graph.edge_finset_bot SimpleGraph.edgeFinset_bot

@[simp]
theorem edgeFinset_sup [DecidableEq V] : (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by
  simp [edgeFinset]
#align simple_graph.edge_finset_sup SimpleGraph.edgeFinset_sup

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]
#align simple_graph.edge_finset_inf SimpleGraph.edgeFinset_inf

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] : (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset :=
  by simp [edgeFinset]
#align simple_graph.edge_finset_sdiff SimpleGraph.edgeFinset_sdiff

theorem edgeFinset_card : G.edgeFinset.card = Fintype.card G.edgeSet :=
  Set.toFinset_card _
#align simple_graph.edge_finset_card SimpleGraph.edgeFinset_card

@[simp]
theorem edgeSet_univ_card : (univ : Finset G.edgeSet).card = G.edgeFinset.card :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset
#align simple_graph.edge_set_univ_card SimpleGraph.edgeSet_univ_card

variable [Fintype V] [DecidableEq V]

@[simp]
theorem edgeFinset_top : (⊤ : SimpleGraph V).edgeFinset = univ.filter fun e => ¬e.IsDiag := by
  rw [← coe_inj]; simp

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
theorem card_edgeFinset_top_eq_card_choose_two :
    (⊤ : SimpleGraph V).edgeFinset.card = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, edgeSet_top, Set.coe_setOf, ← Sym2.card_subtype_not_diag]

/-- Any graph on `n` vertices has at most `n.choose 2` edges. -/
theorem card_edgeFinset_le_card_choose_two : G.edgeFinset.card ≤ (Fintype.card V).choose 2 := by
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl
#align simple_graph.mem_neighbor_set SimpleGraph.mem_neighborSet

lemma not_mem_neighborSet_self : a ∉ G.neighborSet a := by simp
#align simple_graph.not_mem_neighbor_set_self SimpleGraph.not_mem_neighborSet_self

@[simp]
theorem mem_incidenceSet (v w : V) : s(v, w) ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]
#align simple_graph.mem_incidence_set SimpleGraph.mem_incidenceSet

theorem mem_incidence_iff_neighbor {v w : V} : s(v, w) ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v :=
  by simp only [mem_incidenceSet, mem_neighborSet]
#align simple_graph.mem_incidence_iff_neighbor SimpleGraph.mem_incidence_iff_neighbor

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine' ⟨fun h' => _, _⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩
#align simple_graph.adj_incidence_set_inter SimpleGraph.adj_incidenceSet_inter

theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet, compl_adj] at h'
  exact h'.2 h
#align simple_graph.compl_neighbor_set_disjoint SimpleGraph.compl_neighborSet_disjoint

theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ := by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto
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
  simp [and_comm, eq_comm]
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
  simp [commonNeighbors, eq_comm, not_or]
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
  simp [otherVertexOfIncident, Sym2.other_mem']
#align simple_graph.edge_other_incident_set SimpleGraph.edge_other_incident_set

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  cases' h with he hv
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he
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
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [mem_neighborSet, Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw
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
  loopless a := by simp [SDiff.sdiff] -- porting note: used to be handled by `obviously`
#align simple_graph.delete_edges SimpleGraph.deleteEdges

@[simp]
theorem deleteEdges_adj (s : Set (Sym2 V)) (v w : V) :
    (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬s(v, w) ∈ s :=
  Iff.rfl
#align simple_graph.delete_edges_adj SimpleGraph.deleteEdges_adj

theorem sdiff_eq_deleteEdges (G G' : SimpleGraph V) : G \ G' = G.deleteEdges G'.edgeSet := by
  ext
  simp
#align simple_graph.sdiff_eq_delete_edges SimpleGraph.sdiff_eq_deleteEdges

theorem deleteEdges_eq_sdiff_fromEdgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G \ fromEdgeSet s := by
  ext
  exact ⟨fun h => ⟨h.1, not_and_of_not_left _ h.2⟩, fun h => ⟨h.1, not_and'.mp h.2 h.ne⟩⟩
#align simple_graph.delete_edges_eq_sdiff_from_edge_set SimpleGraph.deleteEdges_eq_sdiff_fromEdgeSet

@[simp]
lemma deleteEdges_eq_self {s : Set (Sym2 V)} : G.deleteEdges s = G ↔ Disjoint G.edgeSet s := by
  rw [deleteEdges_eq_sdiff_fromEdgeSet, sdiff_eq_left, disjoint_fromEdgeSet]
#align simple_graph.delete_edges_eq SimpleGraph.deleteEdges_eq_self

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : SimpleGraph V).deleteEdges G.edgeSet := by
  ext
  simp
#align simple_graph.compl_eq_delete_edges SimpleGraph.compl_eq_deleteEdges

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by
  ext
  simp [and_assoc, not_or]
#align simple_graph.delete_edges_delete_edges SimpleGraph.deleteEdges_deleteEdges

@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  simp
#align simple_graph.delete_edges_empty_eq SimpleGraph.deleteEdges_empty_eq

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ := by
  ext
  simp
#align simple_graph.delete_edges_univ_eq SimpleGraph.deleteEdges_univ_eq

theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro
  simp (config := { contextual := true })
#align simple_graph.delete_edges_le SimpleGraph.deleteEdges_le

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [deleteEdges_adj, and_imp, true_and_iff]
  exact fun _ hn hs => hn (h hs)
#align simple_graph.delete_edges_le_of_le SimpleGraph.deleteEdges_le_of_le

theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp (config := { contextual := true }) [imp_false]
#align simple_graph.delete_edges_eq_inter_edge_set SimpleGraph.deleteEdges_eq_inter_edgeSet

theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext v w
  constructor <;> simp (config := { contextual := true }) [@h v w]
#align simple_graph.delete_edges_sdiff_eq_of_le SimpleGraph.deleteEdges_sdiff_eq_of_le

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e
  refine' Sym2.ind _ e
  simp
#align simple_graph.edge_set_delete_edges SimpleGraph.edgeSet_deleteEdges

-- porting note: added `Fintype (Sym2 V)` argument rather than have it be inferred.
-- As a consequence, deleted the `Fintype V` argument.
theorem edgeFinset_deleteEdges [Fintype (Sym2 V)] [DecidableEq V] [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) [DecidableRel (G.deleteEdges s).Adj] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]
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

variable {G}

theorem deleteFar_iff :
    G.DeleteFar p r ↔ ∀ ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj],
      H ≤ G → p H → r ≤ G.edgeFinset.card - H.edgeFinset.card := by
  refine ⟨fun h H _ hHG hH ↦ ?_, fun h s hs hG ↦ ?_⟩
  · have := h (sdiff_subset G.edgeFinset H.edgeFinset)
    simp only [deleteEdges_sdiff_eq_of_le _ hHG, edgeFinset_mono hHG, card_sdiff,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG
#align simple_graph.delete_far_iff SimpleGraph.deleteFar_iff

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff
#align simple_graph.delete_far.le_card_sub_card SimpleGraph.DeleteFar.le_card_sub_card

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG
#align simple_graph.delete_far.mono SimpleGraph.DeleteFar.mono

end DeleteFar

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
  simp
#align simple_graph.card_incidence_set_eq_degree SimpleGraph.card_incidenceSet_eq_degree

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] :
    (G.incidenceFinset v).card = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card
#align simple_graph.card_incidence_finset_eq_degree SimpleGraph.card_incidenceFinset_eq_degree

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset
#align simple_graph.mem_incidence_finset SimpleGraph.mem_incidenceFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = G.edgeFinset.filter (Membership.mem v) := by
  ext e
  refine' Sym2.ind (fun x y => _) e
  simp [mk'_mem_incidenceSet_iff]
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
  rw [degree_compl, h v]
#align simple_graph.is_regular_of_degree.compl SimpleGraph.IsRegularOfDegree.compl

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ _
    (by
      simp_rw [mem_neighborSet]
      infer_instance)
    _
#align simple_graph.neighbor_set_fintype SimpleGraph.neighborSetFintype

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = Finset.univ.filter (G.Adj v) := by
  ext
  simp
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
#align simple_graph.complete_graph_degree SimpleGraph.complete_graph_degree

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  erw [degree, neighborFinset_eq_filter, filter_False]
  exact Finset.card_empty
#align simple_graph.bot_degree SimpleGraph.bot_degree

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  simp
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
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  refine' ⟨v, by simp [minDegree, ht]⟩
#align simple_graph.exists_minimal_degree_vertex SimpleGraph.exists_minimal_degree_vertex

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [minDegree, ht]
#align simple_graph.min_degree_le_degree SimpleGraph.minDegree_le_degree

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h
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
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, _, rfl⟩
  refine' ⟨v, _⟩
  rw [maxDegree, ht]
  rfl
#align simple_graph.exists_maximal_degree_vertex SimpleGraph.exists_maximal_degree_vertex

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [maxDegree, ht]
#align simple_graph.degree_le_max_degree SimpleGraph.degree_le_maxDegree

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [maxDegree, hV, image_empty]
    exact zero_le k
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
  rw [hv]
  apply G.degree_lt_card_verts v
#align simple_graph.max_degree_lt_card_verts SimpleGraph.maxDegree_lt_card_verts

theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (Set.inter_subset_left _ _)
#align simple_graph.card_common_neighbors_le_degree_left SimpleGraph.card_commonNeighbors_le_degree_left

theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]
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
  · rw [Set.mem_toFinset]
    apply not_mem_commonNeighbors_right
  · rw [Finset.insert_subset_iff]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _
#align simple_graph.adj.card_common_neighbors_lt_degree SimpleGraph.Adj.card_commonNeighbors_lt_degree

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]
#align simple_graph.card_common_neighbors_top SimpleGraph.card_commonNeighbors_top

end Finite

end SimpleGraph
