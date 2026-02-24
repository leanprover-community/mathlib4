/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Rel
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an irreflexive symmetric relation.

## Main definitions

* `SimpleGraph` is a structure for symmetric, irreflexive relations.

* `SimpleGraph.neighborSet` is the `Set` of vertices adjacent to a given vertex.

* `SimpleGraph.commonNeighbors` is the intersection of the neighbor sets of two given vertices.

* `SimpleGraph.incidenceSet` is the `Set` of edges containing a given vertex.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `SimpleGraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.

## TODO

* This is the simplest notion of an unoriented graph.
  This should eventually fit into a more complete combinatorics hierarchy which includes
  multigraphs and directed graphs.
  We begin with simple graphs in order to start learning what the combinatorics hierarchy should
  look like.
-/

@[expose] public section

attribute [aesop norm unfold (rule_sets := [SimpleGraph])] Symmetric
attribute [aesop norm (rule_sets := [SimpleGraph])] Std.Irrefl

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
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`
-/
macro (name := aesop_graph?) "aesop_graph?" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop? $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
A variant of `aesop_graph` which does not fail if it is unable to solve the goal.
Use this only for exploration! Nonterminal Aesop is even worse than nonterminal `simp`.
-/
macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, warnOnNonterminal := false })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

open Finset Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph])]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph

initialize_simps_projections SimpleGraph (Adj → adj)

/-- Constructor for simple graphs using a symmetric irreflexive Boolean function. -/
@[simps]
def SimpleGraph.mk' {V : Type u} :
    {adj : V → V → Bool // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ SimpleGraph V where
  toFun x := ⟨fun v w ↦ x.1 v w, fun v w ↦ by simp [x.2.1], ⟨fun v ↦ by simp [x.2.2]⟩⟩
  inj' := by
    intro ⟨adj, _⟩ ⟨adj', _⟩
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
    intro ⟨Adj, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w ↦ Adj v w, ⟨?_, ?_⟩, ?_⟩
    · simp [hs.iff]
    · simp [hi.irrefl]
    · ext
      simp

/-- There are finitely many simple graphs on a given finite type. -/
instance SimpleGraph.instFinite {V : Type u} [Finite V] : Finite (SimpleGraph V) :=
  .of_injective SimpleGraph.Adj fun _ _ ↦ SimpleGraph.ext

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
  symm := fun _ _ ⟨hn, hr⟩ => ⟨hn.symm, hr.symm⟩
  loopless := ⟨fun _ ⟨hn, _⟩ => hn rfl⟩

@[simp]
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.symm
attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.irrefl

instance {V : Type u} [DecidableEq V] (r : V → V → Prop)
    [DecidableRel r] : DecidableRel (SimpleGraph.fromRel r).Adj :=
  inferInstanceAs (DecidableRel fun a b ↦ a ≠ b ∧ (r a b ∨ r b a))

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
def completeBipartiteGraph (V W : Type*) : SimpleGraph (V ⊕ W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm v w := by cases v <;> cases w <;> simp
  loopless := ⟨fun v ↦ by cases v <;> simp⟩

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

@[simp]
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless.irrefl v

theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  ⟨fun x => G.symm x, fun x => G.symm x⟩

@[symm]
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  intro rfl
  exact G.irrefl h

protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h

protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.ne.symm

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)

theorem adj_injective : Injective (Adj : SimpleGraph V → V → V → Prop) :=
  fun _ _ => SimpleGraph.ext

@[simp]
theorem adj_inj {G H : SimpleGraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

theorem adj_congr_of_sym2 {u v w x : V} (h : s(u, v) = s(w, x)) : G.Adj u v ↔ G.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

instance symm_adj (f : ι → V) : Std.Symm fun i j ↦ G.Adj (f i) (f j) where symm _ _ := .symm

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

lemma le_iff_adj {G H : SimpleGraph V} : G ≤ H ↔ ∀ v w, G.Adj v w → H.Adj v w := .rfl

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : SimpleGraph V → SimpleGraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (SimpleGraph V) where
  max x y :=
    { Adj := x.Adj ⊔ y.Adj
      symm _ _ _ := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

@[simp]
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (SimpleGraph V) where
  min x y :=
    { Adj := x.Adj ⊓ y.Adj
      symm _ _ _ := by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

@[simp]
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance : Compl (SimpleGraph V) where
  compl G :=
    { Adj v w := v ≠ w ∧ ¬G.Adj v w
      symm v w h := ⟨h.left.symm, by tauto⟩
      loopless := ⟨fun v h ↦ (h.left rfl).elim⟩ }

@[simp]
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj
      symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }

@[simp]
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj a b := ∃ G ∈ s, Adj G a b
      symm _ _ := Exists.imp fun _ => And.imp_right Adj.symm
      loopless := ⟨fun _ ⟨_, _, ha⟩ ↦ ha.ne rfl⟩ }

instance infSet : InfSet (SimpleGraph V) where
  sInf s :=
    { Adj a b := (∀ ⦃G⦄, G ∈ s → Adj G a b) ∧ a ≠ b
      symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) Ne.symm
      loopless := ⟨fun _ h ↦ h.right rfl⟩ }

@[simp]
theorem sSup_adj {s : Set (SimpleGraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → SimpleGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]

theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SimpleGraph V} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _), Set.forall_mem_range]

instance : PartialOrder (SimpleGraph V) where
  __ := PartialOrder.lift _ adj_injective
  le G H := ∀ ⦃a b⦄, G.Adj a b → H.Adj a b

instance distribLattice : DistribLattice (SimpleGraph V) :=
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SimpleGraph V) where
  top.Adj := Ne
  bot.Adj _ _ := False
  le_top x _ _ h := x.ne_of_adj h
  bot_le _ _ _ h := h.elim
  sdiff_eq x y := by
    ext
    exact ⟨fun h => ⟨h.1, h.ne, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  inf_compl_le_bot _ _ _ h := False.elim <| h.2.2 h.1
  top_le_sup_compl G v w hvw := by
    by_cases h : G.Adj v w
    · exact Or.inl h
    · exact Or.inr ⟨hvw, h⟩
  le_sSup _ G hG _ _ hab := ⟨G, hG, hab⟩
  sSup_le s G hG a b := by
    intro ⟨H, hH, hab⟩
    exact hG _ hH hab
  sInf_le _ _ hG _ _ hab := hab.1 hG
  le_sInf _ _ hG _ _ hab := ⟨fun _ hH => hG _ hH hab, hab.ne⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]
/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices. -/
abbrev completeGraph (V : Type u) : SimpleGraph V := ⊤

/-- The graph with no edges on a given vertex type `V`. -/
abbrev emptyGraph (V : Type u) : SimpleGraph V := ⊥

@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl

@[simp]
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

variable {G}

set_option backward.isDefEq.respectTransparency false in
theorem eq_bot_iff_forall_not_adj : G = ⊥ ↔ ∀ a b : V, ¬G.Adj a b := by
  simp [← le_bot_iff, le_iff_adj]

theorem ne_bot_iff_exists_adj : G ≠ ⊥ ↔ ∃ a b : V, G.Adj a b := by
  simp [eq_bot_iff_forall_not_adj]

set_option backward.isDefEq.respectTransparency false in
theorem eq_top_iff_forall_ne_adj : G = ⊤ ↔ ∀ a b : V, a ≠ b → G.Adj a b := by
  simp [← top_le_iff, le_iff_adj]

theorem ne_top_iff_exists_not_adj : G ≠ ⊤ ↔ ∃ a b : V, a ≠ b ∧ ¬G.Adj a b := by
  simp [eq_top_iff_forall_ne_adj]

variable (G)

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

instance uniqueOfSubsingleton [Subsingleton V] : Unique (SimpleGraph V) where
  default := ⊥
  uniq G := by ext a b; simp [Subsingleton.elim a b]

instance [Nontrivial V] : Nontrivial (SimpleGraph V) :=
  ⟨⊥, ⊤, fun h ↦ not_subsingleton V ⟨by simpa only [← adj_inj, funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w ∧ ¬G.Adj v w

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V :=
  SetRel.dom {(u, v) : V × V | G.Adj u v}

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w :=
  Iff.rfl

theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  SetRel.dom_mono fun _uv huv ↦ h huv

/-- All vertices are in the support of the complete graph if there is more than one vertex. -/
@[simp]
theorem support_top_of_nontrivial [Nontrivial V] : (⊤ : SimpleGraph V).support = Set.univ :=
  Set.eq_univ_of_forall fun v₁ => exists_ne v₁ |>.imp fun _v₂ h => h.symm

/-- The support of the empty graph is empty. -/
@[simp]
theorem support_bot : (⊥ : SimpleGraph V).support = ∅ :=
  SetRel.dom_eq_empty_iff.mpr <| Set.empty_def.symm

/-- Only the empty graph has empty support. -/
@[simp]
theorem support_eq_bot_iff : G.support = ∅ ↔ G = ⊥ :=
  ⟨fun h ↦ eq_bot_iff_forall_not_adj.mpr fun v w nadj ↦
    Set.ext_iff.mp (SetRel.dom_eq_empty_iff.mp h) (v, w) |>.mp nadj |>.elim,
   (· ▸ support_bot)⟩

/-- The support of a graph is empty if there at most one vertex. -/
@[simp]
theorem support_of_subsingleton [Subsingleton V] : G.support = ∅ :=
  uniqueOfSubsingleton.uniq G ▸ support_bot

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def neighborSet (v : V) : Set V := {w | G.Adj v w}

instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)

lemma neighborSet_subset_support (v : V) : G.neighborSet v ⊆ G.support :=
  fun _ hadj ↦ ⟨v, hadj.symm⟩

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `Iff.rfl`.
(That is, `s(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- Porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h => Sym2.ind h⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

@[simp]
theorem mem_edgeSet : s(v, w) ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl

theorem not_isDiag_of_mem_edgeSet : e ∈ edgeSet G → ¬e.IsDiag :=
  Sym2.ind (fun _ _ => Adj.ne) e

@[simp] lemma not_mem_edgeSet_of_isDiag : e.IsDiag → e ∉ edgeSet G :=
  imp_not_comm.1 G.not_isDiag_of_mem_edgeSet

alias _root_.Sym2.IsDiag.not_mem_edgeSet := not_mem_edgeSet_of_isDiag

theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ :=
  (edgeSetEmbedding V).le_iff_le

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ :=
  (edgeSetEmbedding V).lt_iff_lt

theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  (edgeSetEmbedding V).injective

@[gcongr] alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

@[gcongr] alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot

@[simp]
theorem edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ :=
  Sym2.diagSet_compl_eq_fromRel_ne.symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem edgeSet_subset_compl_diagSet : G.edgeSet ⊆ Sym2.diagSetᶜ := by
  simpa [Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding] using G.loopless

@[deprecated (since := "2025-12-10")]
alias edgeSet_subset_setOf_not_isDiag := edgeSet_subset_compl_diagSet

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

variable {G G₁ G₂}

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edgeSet_inf, ← edgeSet_bot, ← Set.le_iff_subset,
    OrderEmbedding.le_iff_le]

@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]

@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_fromEdgeSet`,
allows proving `(G \ fromEdgeSet s).edgeSet = G.edgeSet \ s` by `simp`. -/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \ s := by
  grind [Sym2.mem_diagSet, not_isDiag_of_mem_edgeSet]

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = s(a, b) := by
  simp

variable (G G₁ G₂)

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  rw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm

instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _

instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/-- `fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops. -/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm _ _ h := ⟨Sym2.toRel_symmetric s h.1, h.2.symm⟩

instance [DecidablePred (· ∈ s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ s(v, w) ∈ s ∧ v ≠ w

@[simp]
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) ∈ s ∧ v ≠ w :=
  Iff.rfl

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet := by
  ext e
  exact Sym2.ind (by simp) e

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

@[simp] lemma fromEdgeSet_le {s : Set (Sym2 V)} :
    fromEdgeSet s ≤ G ↔ s \ Sym2.diagSet ⊆ G.edgeSet := by simp [← edgeSet_subset_edgeSet]

set_option backward.isDefEq.respectTransparency false in
lemma edgeSet_eq_iff : G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagSet where
  mp := by intro rfl; simp +contextual [Set.disjoint_right]
  mpr := by rintro ⟨rfl, hs⟩; simp [hs]

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext
  simp

@[simp] lemma fromEdgeSet_not_isDiag : @fromEdgeSet V Sym2.diagSetᶜ = ⊤ := by ext; simp

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext
  simp

@[simp]
theorem fromEdgeSet_inter (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∩ t) = fromEdgeSet s ⊓ fromEdgeSet t := by
  ext
  simp
  tauto

@[simp]
theorem fromEdgeSet_union (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∪ t) = fromEdgeSet s ⊔ fromEdgeSet t := by
  ext
  simp [or_and_right]

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t := by
  ext
  constructor <;> simp +contextual

@[gcongr, mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  simpa using Set.diff_subset_diff h fun _ a ↦ a

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  conv_rhs => rw [← Set.diff_union_inter s Sym2.diagSet]
  rw [← disjoint_edgeSet, edgeSet_fromEdgeSet]
  grind [edgeSet_subset_compl_diagSet]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm, disjoint_fromEdgeSet, disjoint_comm]

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet

set_option backward.isDefEq.respectTransparency false in
theorem disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ ∀ x y, G.Adj x y → ¬H.Adj x y := by
  simp [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1

theorem mk'_mem_incidenceSet_iff : s(b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff

theorem mk'_mem_incidenceSet_left_iff : s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_left _ _

theorem mk'_mem_incidenceSet_right_iff : s(a, b) ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_right _ _

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {s(a, b)} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {s(a, b)} := by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  intro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G.edgeSet ∧ v ∈ e

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl

lemma notMem_neighborSet_self : a ∉ G.neighborSet a := by simp

@[simp]
theorem mem_incidenceSet (v w : V) : s(v, w) ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]

theorem mem_incidence_iff_neighbor {v w : V} :
    s(v, w) ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v := by
  simp

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · intro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩

set_option backward.isDefEq.respectTransparency false in
theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  intro w ⟨h, h'⟩
  exact h'.2 h

theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ := by
  ext
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v ∪ Gᶜ.neighborSet v : Set V)] :
    #(G.neighborSet v ∪ Gᶜ.neighborSet v).toFinset = Fintype.card V - 1 := by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]

theorem neighborSet_compl (G : SimpleGraph V) (v : V) :
    Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v} := by
  ext
  simp [and_comm, eq_comm]

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _

theorem notMem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl

theorem notMem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) :=
  inferInstanceAs <| DecidablePred fun u => u ∈ G.neighborSet v ∧ u ∈ G.neighborSet w

theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext
  simp [commonNeighbors, eq_comm]

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

@[simp]
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    rw [Subtype.mk.injEq, incidence_other_neighbor_edge _ hw]

end Incidence

section IsCompleteBetween

variable {s t : Set V}

/-- The condition that the portion of the simple graph `G` _between_ `s` and `t` is complete, that
is, every vertex in `s` is adjacent to every vertex in `t`, and vice versa. -/
def IsCompleteBetween (G : SimpleGraph V) (s t : Set V) :=
  ∀ ⦃v₁⦄, v₁ ∈ s → ∀ ⦃v₂⦄, v₂ ∈ t → G.Adj v₁ v₂

theorem IsCompleteBetween.disjoint (h : G.IsCompleteBetween s t) : Disjoint s t :=
  Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless.irrefl v) (h hv₁ hv₂)

theorem isCompleteBetween_comm : G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  mp h _ h₁ _ h₂ := (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm

end IsCompleteBetween

section Subsingleton

protected theorem subsingleton_iff : Subsingleton (SimpleGraph V) ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Unique.instSubsingleton⟩
  contrapose! h
  exact instNontrivial

protected theorem nontrivial_iff : Nontrivial (SimpleGraph V) ↔ Nontrivial V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ instNontrivial⟩
  contrapose! h
  exact Unique.instSubsingleton

end Subsingleton

end SimpleGraph
