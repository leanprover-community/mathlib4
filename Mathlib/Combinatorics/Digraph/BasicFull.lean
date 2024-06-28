/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton
-/
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`.

## Main definitions

* `Digraph` is a structure for the relation

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.

## Todo

* The implementation of digraphs is currently incomplete. It was originally created by Kyle Miller
using an older version of Mathlib. This version of the module is being ported into the current
version of Mathlib by Jack Cheverton. Furthermore, new additions to the module are being made
based on what has been added to SimpleGraph since the original implementation of Digraph was
created.
-/

open Finset Function

universe u v w

/-- A directed graph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
-/
@[ext]
structure Digraph (V : Type u) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop

noncomputable instance {V : Type u} [Fintype V] : Fintype (Digraph V) := by
  classical exact Fintype.ofInjective Digraph.Adj Digraph.ext

/-- Constructor for digraphs using a boolean function. -/
@[simps]
def Digraph.mk' {V : Type u} :
    (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' := by
    intro adj adj'
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w

/-- Construct the digraph induced by the given relation. -/
def Digraph.fromRel {V : Type u} (r : V → V → Prop) : Digraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)

@[simp]
theorem Digraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (Digraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

/-- The complete graph on a type `V` is the digraph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def Digraph.completeGraph (V : Type u) : Digraph V where Adj := ⊤

/-- The graph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def Digraph.emptyGraph (V : Type u) : Digraph V where Adj _ _ := False

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
def Digraph.completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

namespace Digraph

variable {ι : Sort _} {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : Digraph V)
  (G' : Digraph W) {a b c u v w : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) :=
  Digraph.ext

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

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Sup (Digraph V) where
  sup x y :=
    { Adj := x.Adj ⊔ y.Adj }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (Digraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance hasCompl : HasCompl (Digraph V) where
  compl G :=
    { Adj := fun v w => ¬G.Adj v w }

@[simp]
theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s :=
    { Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) }

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

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { show DistribLattice (Digraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeBooleanAlgebra : CompleteBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w _ => trivial
    bot_le := fun x v w h => h.elim
    sdiff_eq := fun x y => by
      ext (v w)
      exact Iff.rfl
    inf_compl_le_bot := fun G v w h => False.elim <| h.2 h.1
    top_le_sup_compl := fun G v w _ => by
      by_cases h : G.Adj v w
      · exact Or.inl h
      · exact Or.inr h
    sSup := sSup
    le_sSup := fun s G hG a b hab => ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b => by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab => hab hG
    le_sInf := fun s G hG a b hab => fun H hH => hG _ hH hab
    inf_sSup_le_iSup_inf := fun G s a b hab => by simpa using hab
    iInf_sup_le_sup_sInf := fun G s a b hab => by
      simpa [forall_and, forall_or_left, or_and_right] using hab }

@[simp]
theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp]
theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type u) : Inhabited (Digraph V) :=
  ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

instance [Nontrivial V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  rw [← completeGraph_eq_top, ← emptyGraph_eq_bot, Digraph.completeGraph, Digraph.emptyGraph]
  simp only [ne_eq, mk.injEq]
  rw [← @Ne.eq_def, @ne_iff]
  simp only [Pi.top_apply, ne_eq, exists_const]
  rw [← @Ne.eq_def, @ne_iff]
  simp only [Pi.top_apply, Prop.top_eq_true, ne_eq, eq_iff_iff, iff_true, not_false_eq_true,
    exists_const]

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

end Decidable

end Order




-------------------------------------------------------------
---- BREAK --------------------------------------------------
-------------------------------------------------------------




/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V :=
  Rel.dom G.Adj

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w :=
  Iff.rfl

theorem support_mono {G G' : Digraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  Rel.dom_mono h

/-- `G.inNeighborSet v` is the set of vertices `v` is adjacent to in `G`. -/
def inNeighborSet (v : V) : Set V := {w | G.Adj w v}

/-- `G.outNeighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def outNeighborSet (v : V) : Set V := {w | G.Adj v w}

/-- `G.neighborSet v` is the union of `G.inNeighborSet v` and `G.outNeighborSet v`. -/
def neighborSet (v : V) : Set V := G.inNeighborSet v ∪ G.outNeighborSet v

/-
instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)
#align simple_graph.neighbor_set.mem_decidable Digraph.neighborSet.memDecidable
-/

section EdgeSet

variable {G₁ G₂ : Digraph V}

/-- The edges of G consist of the ordered pairs of vertices related by
`G.Adj`. This is the order isomorphism; for the edge set of a particular graph, see
`Digraph.edgeSet`.
-/
def edgeSetIso (V : Type _) : Digraph V ≃o Set (V × V) where
  toFun G := {e | G.Adj e.1 e.2}
  invFun s := ⟨fun v w ↦ (v, w) ∈ s⟩
  left_inv := by intro G; simp
  right_inv := by intro s; simp
  map_rel_iff' := by intro G G'; simp only [Equiv.coe_fn_mk, Set.le_eq_subset,
  Set.setOf_subset_setOf, Prod.forall]; apply Iff.rfl

@[simp]
lemma edgeSetIso_symm_adj {s : Set (V × V)} : ((edgeSetIso V).symm s).Adj v w ↔
  (v, w) ∈ s := Iff.rfl

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetIso G` that permits dot notation. -/
abbrev edgeSet (G : Digraph V) : Set (V × V) := edgeSetIso V G

@[simp]
theorem mem_edgeSet : (v, w) ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl

theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetIso V).eq_iff_eq

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ :=
  (edgeSetIso V).le_iff_le

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ :=
  (edgeSetIso V).lt_iff_lt

theorem edgeSet_injective : Injective (edgeSet : Digraph V → Set (V × V)) :=
  (edgeSetIso V).injective

alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : Digraph V).edgeSet = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  simp

-- JACK: This should work? I'm trying to say that the edgeset of the top digraph is all possible
-- edges between vertices V
@[simp]
theorem edgeSet_top : (⊤ : Digraph V).edgeSet = {e | (⊤ : Digraph V).Adj e.1 e.2} := by
  ext ⟨x, y⟩
  rfl

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


@[simp] lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edgeSet_inf, ← edgeSet_bot, ← Set.le_iff_subset,
    OrderIso.le_iff_le (edgeSetIso V)]

@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]

@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]

-- JACK: is this definition correct?
/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ ∃ e ∈ G.edgeSet, e = (v, w) := by
  constructor
  · intro h
    simp only [Prod.exists, mem_edgeSet, Prod.mk.injEq]
    use v, w
  · intro h
    obtain ⟨e, he⟩ := h
    cases' he with he1 he2
    rw [← @mem_edgeSet, ← he2]
    exact he1

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = (a, b) := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]

variable (G G₁ G₂)

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  fun x => inferInstanceAs <| Decidable (G.Adj x.1 x.2)

instance fintypeEdgeSet [Fintype V] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _

instance fintypeEdgeSetBot : Fintype (⊥ : Digraph V).edgeSet := by
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

variable (s : Set (V × V))

/-- `fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops. -/
def fromEdgeSet : Digraph V where
  Adj a b := (a, b) ∈ s

@[simp]
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ (v, w) ∈ s :=
  Iff.rfl

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s := by rfl

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by rfl

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (V × V)) = ⊥ := by rfl

@[simp]
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (V × V)) = ⊤ := by rfl

@[simp]
theorem fromEdgeSet_inter (s t : Set (V × V)) :
    fromEdgeSet (s ∩ t) = fromEdgeSet s ⊓ fromEdgeSet t := by rfl

@[simp]
theorem fromEdgeSet_union (s t : Set (V × V)) :
    fromEdgeSet (s ∪ t) = fromEdgeSet s ⊔ fromEdgeSet t := by rfl

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (V × V)) :
    fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t := by rfl

@[mono]
theorem fromEdgeSet_mono {s t : Set (V × V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  rintro v w
  simp (config := { contextual := true }) only [fromEdgeSet_adj, Ne, not_false_iff,
    and_true_iff, and_imp]
  exact fun a ↦ h a

@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  constructor
  · intro h
    rw [← @disjoint_edgeSet, @edgeSet_fromEdgeSet] at h
    exact h
  · intro h
    rw [← @disjoint_edgeSet, @edgeSet_fromEdgeSet]
    exact h

@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm, disjoint_fromEdgeSet, disjoint_comm]

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet


/-! ### Incidence set -/

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidenceSet (v : V) : Set (V × V) :=
  { e ∈ G.edgeSet | v = e.1 ∨ v = e.2}

theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1

theorem mk'_mem_incidenceSet_iff : (b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  Set.mem_def

theorem mk'_mem_incidenceSet_left_iff : (a, b) ∈ G.incidenceSet a ↔ G.Adj a b := by
  rw [@mk'_mem_incidenceSet_iff]
  constructor
  · intro h
    cases' h with h1 h2
    exact h1
  · intro h
    constructor
    · exact h
    · left
      rfl

theorem mk'_mem_incidenceSet_right_iff : (a, b) ∈ G.incidenceSet b ↔ G.Adj a b := by
  rw [@mk'_mem_incidenceSet_iff]
  constructor
  · intro h
    cases' h with h1 h2
    exact h1
  · intro h
    constructor
    · exact h
    · right
      rfl

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a = (e : V × V).1 ∨ a
  = (e : V × V).2 := and_iff_right e.2

theorem adj_of_mem_incidenceSet (e : V × V) (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
  (hb : e ∈ G.incidenceSet b) : G.Adj a b ∨ G.Adj b a := by
  rw [incidenceSet] at ha hb
  simp only [Set.sep_or, Set.mem_union, Set.mem_setOf_eq] at ha hb
  cases' ha with ha1 ha2
  · cases' ha1 with ha11 ha12
    · cases' hb with hb1 hb2
      · cases' hb1 with hb11 hb12
        have H : a = b := by
          rw [ha12, ← hb12]
        contradiction
      · left
        cases' hb2 with hb21 hb22
        have h3 : e = (a, b) := by rw [ha12, hb22]
        rw [h3] at hb21
        exact hb21
  · cases' hb with hb1 hb2
    · cases' ha2 with ha21 ha22
      cases' hb1 with hb11 hb12
      right
      have h3 : e = (b, a) := by rw [ha22, hb12]
      rw [h3] at ha21
      exact ha21
    · cases' ha2 with ha21 ha22
      cases' hb2 with hb21 hb22
      have h3 : a = b := by rw [hb22, ha22]
      contradiction

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) := by
  rw [incidenceSet]
  simp only [Set.sep_or, Set.mem_union, Set.mem_setOf_eq]
  rw [DecidablePred]
  intro e
  exact instDecidableOr

@[simp]
theorem mem_inNeighborSet (v w : V) : w ∈ G.inNeighborSet v ↔ G.Adj w v :=
  Iff.rfl

@[simp]
theorem mem_outNeighborSet (v w : V) : w ∈ G.outNeighborSet v ↔ G.Adj v w :=
  Iff.rfl

@[simp]
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔
  w ∈ G.inNeighborSet v ∪ G.outNeighborSet v := Iff.rfl

@[simp]
theorem mem_incidenceSet (v w : V) : (v, w) ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]
  intro h1 h2
  rw [h2] at h1 ⊢
  exact h1

theorem mem_incidence_iff_inNeighbor {v w : V} :
    (v, w) ∈ G.incidenceSet v ↔ v ∈ G.inNeighborSet w := by
  simp only [mem_incidenceSet, mem_inNeighborSet]

theorem mem_incidence_iff_outNeighbor {v w : V} :
    (v, w) ∈ G.incidenceSet v ↔ w ∈ G.outNeighborSet v := by
  simp only [mem_incidenceSet, mem_outNeighborSet]

theorem compl_inNeighborSet_disjoint (G : Digraph V) (v : V) :
    Disjoint (G.inNeighborSet v) (Gᶜ.inNeighborSet v) := by
  rw [Disjoint, @Set.bot_eq_empty]
  intro x h1 h2
  rw [inNeighborSet] at h1 h2
  have H : {w | Gᶜ.Adj w v} = {w | ¬G.Adj w v} := rfl
  rw [H] at h2
  rw [@Set.le_iff_subset] at *
  have H1 : {w | G.Adj w v} ∩ {w | ¬G.Adj w v} = ∅ := by
    rw [← @Set.disjoint_iff_inter_eq_empty]
    exact Set.disjoint_left.mpr fun ⦃v⦄ v_1 v ↦ v v_1
  have h3 : x ⊆ {w | G.Adj w v} ∩ {w | ¬G.Adj w v} := Set.subset_inter h1 h2
  rw [H1] at h3
  exact h3

theorem compl_outNeighborSet_disjoint (G : Digraph V) (v : V) :
    Disjoint (G.outNeighborSet v) (Gᶜ.outNeighborSet v) := by
  rw [Disjoint, @Set.bot_eq_empty]
  intro x h1 h2
  rw [outNeighborSet] at h1 h2
  have H : {w | Gᶜ.Adj v w} = {w | ¬G.Adj v w} := rfl
  rw [H] at h2
  rw [@Set.le_iff_subset] at *
  have H1 : {w | G.Adj v w} ∩ {w | ¬G.Adj v w} = ∅ := by
    rw [← @Set.disjoint_iff_inter_eq_empty]
    exact Set.disjoint_left.mpr fun ⦃v⦄ v_1 v ↦ v v_1
  have h3 : x ⊆ {w | G.Adj v w} ∩ {w | ¬G.Adj v w} := Set.subset_inter h1 h2
  rw [H1] at h3
  exact h3

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔
  (G.Adj v u ∨ G.Adj u v) ∧ (G.Adj w u ∨ G.Adj u w) := by
    rw [commonNeighbors, neighborSet, neighborSet, inNeighborSet, outNeighborSet,
    inNeighborSet, outNeighborSet]
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro h
      cases' h with h1 h2
      constructor
      · cases' h1 with h11 h12
        · right
          exact h11
        · left
          exact h12
      · cases' h2 with h21 h22
        · right
          exact h21
        · left
          exact h22
    · intro h
      cases' h with h1 h2
      constructor
      · cases' h1 with h11 h12
        · right
          exact h11
        · left
          exact h12
      · cases' h2 with h21 h22
        · right
          exact h21
        · left
          exact h22

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) := by
  rw [commonNeighbors]
  simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_union, mem_inNeighborSet,
    mem_outNeighborSet]
  rw [DecidablePred]
  intro e
  exact instDecidableAnd


section Incidence

variable [DecidableEq V]

theorem edge_other_incident_set {e : V × V} : e ∈ G.incidenceSet e.1 ↔
e ∈ G.incidenceSet e.2 := by
  rw [incidenceSet, incidenceSet]
  simp only [Set.sep_or, Set.mem_union, Set.mem_setOf_eq, and_true]
  rw [@Set.mem_def]
  constructor
  · intro h
    cases' h with h1 h2
    · right
      exact h1
    · left
      cases' h2 with h21 h22
      constructor
      · exact h21
      · rw [h22]
  · intro h
    cases' h with h1 h2
    · cases' h1 with h11 h12
      left
      exact h11
    · left
      exact h2

end Incidence


/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `Digraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (V × V)) := G \ fromEdgeSet s

variable {H : Digraph V} {s s₁ s₂ : Set (V × V)}


@[simp]
theorem deleteEdges_adj (s : Set (V × V)) (v w : V) :
    (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬(v, w) ∈ s :=
  Iff.rfl

@[simp] lemma deleteEdges_edgeSet (G G' : Digraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp

@[simp] lemma deleteEdges_empty : G.deleteEdges ∅ = G := by simp [deleteEdges]
@[simp] lemma deleteEdges_univ : G.deleteEdges Set.univ = ⊥ := by simp [deleteEdges]



lemma deleteEdges_anti (h : s₁ ⊆ s₂) : G.deleteEdges s₂ ≤ G.deleteEdges s₁ :=
  sdiff_le_sdiff_left $ fromEdgeSet_mono h

--lemma deleteEdges_mono (h : G ≤ H) : G.deleteEdges s ≤ H.deleteEdges s := sdiff_le_sdiff_right h

lemma deleteEdges_mono (h : G ≤ H) : G.deleteEdges s ≤ H.deleteEdges s := by
  apply sdiff_le_sdiff_right h


theorem sdiff_eq_deleteEdges (G G' : Digraph V) : G \ G' = G.deleteEdges G'.edgeSet := by
  ext
  simp

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : Digraph V).deleteEdges G.edgeSet := by
  ext
  simp

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (V × V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by
  ext
  simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  simp

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ := by
  ext
  simp

theorem deleteEdges_le (s : Set (V × V)) : G.deleteEdges s ≤ G := by
  intro
  simp (config := { contextual := true })


theorem deleteEdges_le_of_le {s s' : Set (V × V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [deleteEdges_adj, and_imp, true_and_iff]
  exact fun _ hn hs => hn (h hs)

theorem deleteEdges_eq_inter_edgeSet (s : Set (V × V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp (config := { contextual := true }) [imp_false]

theorem deleteEdges_sdiff_eq_of_le {H : Digraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext (v w)
  constructor <;> simp (config := { contextual := true }) [@h v w]

theorem edgeSet_deleteEdges (s : Set (V × V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e
  cases e
  simp


/-! ## Map and comap -/


/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `Digraph.map_injective`). -/
protected def map (f : V → W) (G : Digraph V) : Digraph W where
  Adj := Relation.Map G.Adj f f

@[simp]
theorem map_adj (f : V → W) (G : Digraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

theorem map_monotone (f : V → W) : Monotone (Digraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `Digraph.induce` for a wrapper.

This is surjective when `f` is injective (see `Digraph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : Digraph V where
  Adj u v := G.Adj (f u) (f v)

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

theorem map_le_iff_le_comap (f : V ↪ W) (G : Digraph V) (G' : Digraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V ↪ W) (G : Digraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `Digraph V` and `Digraph s`.

There is also a notion of induced subgraphs (see `Digraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `Digraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : Digraph V) : Digraph s :=
  G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `Digraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `Digraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : Digraph s) : Digraph V :=
  G.map (Function.Embedding.subtype _)

theorem induce_spanningCoe {s : Set V} {G : Digraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _


section Maps

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
#align simple_graph.hom Digraph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj

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

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h

theorem map_mem_edgeSet {e : V × V} (h : e ∈ G.edgeSet) : e.map f f ∈ G'.edgeSet := by
  cases e
  exact f.map_rel' h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Prod.map f f e, f.map_mem_edgeSet e.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : Digraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat' rw [Subtype.mk_eq_mk]
  cases e₁
  cases e₂
  simp only [Prod.mk.injEq, and_imp]
  intro h1 h2
  simp [hinj h1, hinj h2]

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `Digraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

variable {G'' : Digraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edgeSet_iff {e : V × V} : e.map f f ∈ G'.edgeSet ↔ e ∈ G.edgeSet := by
  cases e
  simp [f.map_adj_iff]

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.injective

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : Digraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem comap_apply (f : V ↪ W) (G : Digraph W) (v : V) :
  Digraph.Embedding.comap f G v = f v := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : Digraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

@[simp]
theorem map_apply (f : V ↪ W) (G : Digraph V) (v : V) :
  Digraph.Embedding.map f G v = f v := rfl

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  Digraph.Embedding.comap (Function.Embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : Digraph s) : G ↪g G.spanningCoe :=
  Digraph.Embedding.map (Function.Embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ↪ β) :
    (⊤ : Digraph α) ↪g (⊤ : Digraph β) :=
  { f with map_rel_iff' := by simp }

variable {G'' : Digraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Embedding

section InduceHom

variable {G G'} {G'' : Digraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def InduceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

@[simp, norm_cast] lemma coe_induceHom : ⇑(InduceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl

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

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  RelIso.symm f

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edgeSet_iff {e : V × V} : e.map f f ∈ G'.edgeSet ↔ e ∈ G.edgeSet := by
  cases e
  simp [f.map_adj_iff]

theorem card_eq_of_iso [Fintype V] [Fintype W] (f : G ≃g G') : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  -- porting note: need to help it to find the typeclass instances from the target expression
  apply @Fintype.card_congr' _ _ (_) (_) rfl

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : Digraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma comap_apply (f : V ≃ W) (G : Digraph W) (v : V) :
  Digraph.Iso.comap f G v = f v := rfl

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : Digraph W) (w : W) :
  (Digraph.Iso.comap f G).symm w = f.symm w := rfl

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : Digraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

@[simp]
lemma map_apply (f : V ≃ W) (G : Digraph V) (v : V) :
  Digraph.Iso.map f G v = f v := rfl

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : Digraph V) (w : W) :
  (Digraph.Iso.map f G).symm w = f.symm w := rfl

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ≃ β) :
    (⊤ : Digraph α) ≃g (⊤ : Digraph β) :=
  { f with map_rel_iff' := by simp }

theorem toEmbedding_completeGraph {α β : Type _} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

variable {G'' : Digraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Iso

end Maps

end Digraph
