/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.GraphLike.Walks.Dart

/-!
# Walks

This file separates the graph-independent data of a walk from its proof of validity in a
graph-like structure. A `WalkData` records vertices, edges, and the exact ordered pairs of
incidences used by its steps. `WalkData.IsValid` certifies that data in a particular graph, and
`Walk G u v` packages valid data with specified endpoints.

## Main definitions

* `HyperGraphLike.WalkData`: graph-independent walk data
* `HyperGraphLike.WalkData.IsValid`: validity of walk data in a graph
* `HyperGraphLike.Walk`: valid walk data with indexed endpoints
* `HyperGraphLike.Walk.ofIncidencePairs` / `ofEdges` / `ofVertices`: construct a walk from
  incidence pairs, edges, or vertices under the corresponding uniqueness hypotheses

## Tags

walks
-/

public section

namespace HyperGraphLike

variable {V I E Gr : Type*} {u v w x : V} {G : Gr} {i j : I} {e : E} [HyperGraphLike V I E Gr]

/-- A graph-independent alternating sequence
`[v₀, i₁, e₁, j₁, v₁, ..., iₙ, eₙ, jₙ, vₙ]`.

The constructor stores both incidences of every traversal, so different choices of incidences are
not identified even when they have the same vertices and edge. -/
inductive WalkData (V I E : Type*) : Type _
  | nil (u : V) : WalkData V I E
  | cons (u : V) (sourceInc : I) (edge : E) (targetInc : I) (tail : WalkData V I E) : WalkData V I E
deriving DecidableEq, Inhabited

namespace WalkData

variable {p q : WalkData V I E}

/-- The initial vertex of walk data. -/
@[expose] def first : WalkData V I E → V
  | nil u => u
  | cons u _ _ _ _ => u

@[simp, grind =] lemma first_nil : (nil u : WalkData V I E).first = u := rfl

@[simp, grind =] lemma first_cons : (cons u i e j p).first = u := rfl

/-- The final vertex of walk data. -/
@[expose] def last : WalkData V I E → V
  | nil u => u
  | cons _ _ _ _ p => p.last

@[simp, grind =] lemma last_nil : (nil u : WalkData V I E).last = u := rfl

@[simp, grind =] lemma last_cons : (cons u i e j p).last = p.last := rfl

/-- The number of traversals in walk data. -/
@[expose] def length : WalkData V I E → ℕ
  | nil _ => 0
  | cons _ _ _ _ p => p.length + 1

@[simp, grind =] lemma length_nil : (nil u : WalkData V I E).length = 0 := rfl

@[simp, grind =] lemma length_cons : (cons u i e j p).length = p.length + 1 := rfl

/-- The vertices visited by walk data, in order. -/
@[expose] def vertices : WalkData V I E → List V
  | nil u => [u]
  | cons u _ _ _ p => u :: p.vertices

@[simp, grind =] lemma vertices_nil : (nil u : WalkData V I E).vertices = [u] := rfl

@[simp, grind =] lemma vertices_cons : (cons u i e j p).vertices = u :: p.vertices := rfl

/-- The edges traversed by walk data, in order. -/
@[expose] def edges : WalkData V I E → List E
  | nil _ => []
  | cons _ _ e _ p => e :: p.edges

@[simp, grind =] lemma edges_nil : (nil u : WalkData V I E).edges = [] := rfl

@[simp, grind =] lemma edges_cons : (cons u i e j p).edges = e :: p.edges := rfl

/-- The ordered pairs of source and target incidences used by walk data, in order. -/
@[expose] def incidencePairs : WalkData V I E → List (I × I)
  | nil _ => []
  | cons _ i _ j p => (i, j) :: p.incidencePairs

@[simp, grind =]
lemma incidencePairs_nil : (nil u : WalkData V I E).incidencePairs = [] := rfl

@[simp, grind =]
lemma incidencePairs_cons : (cons u i e j p).incidencePairs = (i, j) :: p.incidencePairs := rfl

/-- The source incidences used by walk data, in order. -/
@[expose] def sourceIncs : WalkData V I E → List I
  | nil _ => []
  | cons _ i _ _ p => i :: p.sourceIncs

@[simp, grind =] lemma sourceIncs_nil : (nil u : WalkData V I E).sourceIncs = [] := rfl

@[simp, grind =] lemma sourceIncs_cons : (cons u i e j p).sourceIncs = i :: p.sourceIncs := rfl

/-- The target incidences used by walk data, in order. -/
@[expose] def targetIncs : WalkData V I E → List I
  | nil _ => []
  | cons _ _ _ j p => j :: p.targetIncs

@[simp, grind =] lemma targetIncs_nil : (nil u : WalkData V I E).targetIncs = [] := rfl

@[simp, grind =] lemma targetIncs_cons : (cons u i e j p).targetIncs = j :: p.targetIncs := rfl

/-- A walk's three aligned data lists determine it. -/
@[ext]
theorem ext (hs : p.vertices = q.vertices) (he : p.edges = q.edges)
    (hi : p.incidencePairs = q.incidencePairs) : p = q := by
  induction p generalizing q <;> cases q <;> grind

@[simp, grind =] lemma mem_nil_iff : x ∈ (nil u : WalkData V I E).vertices ↔ x = u := by grind

@[simp, grind =] lemma mem_cons_iff : x ∈ (cons u i e j p).vertices ↔ x = u ∨ x ∈ p.vertices := by
  grind

@[simp, grind .] lemma first_mem (p : WalkData V I E) : p.first ∈ p.vertices := by cases p <;> grind

@[simp, grind .] lemma last_mem (p : WalkData V I E) : p.last ∈ p.vertices := by
  induction p <;> grind

@[simp, grind .] lemma vertices_ne_nil (p : WalkData V I E) : p.vertices ≠ [] := by
  cases p <;> grind

@[simp, grind =]
lemma vertices_head (p : WalkData V I E) : p.vertices.head p.vertices_ne_nil = p.first := by
  cases p <;> grind

@[simp, grind =] lemma vertices_head? (p : WalkData V I E) : p.vertices.head? = some p.first := by
  cases p <;> rfl

@[simp, grind =]
lemma vertices_getLast (p : WalkData V I E) : p.vertices.getLast p.vertices_ne_nil = p.last := by
  induction p <;> grind

/-- The set of vertices visited by walk data. -/
@[expose] def vertexSet (p : WalkData V I E) : Set V := {x | x ∈ p.vertices}

@[simp, grind =] lemma vertexSet_nil : (nil u : WalkData V I E).vertexSet = {u} := by
  ext; simp [vertexSet]

@[simp, grind =] lemma vertexSet_cons : (cons u i e j p).vertexSet = insert u p.vertexSet := by
  ext; simp [vertexSet]

@[simp, grind =] lemma mem_vertexSet : x ∈ p.vertexSet ↔ x ∈ p.vertices := Iff.rfl

theorem vertexSet_finite (p : WalkData V I E) : p.vertexSet.Finite := List.finite_toSet _

/-- The set of edges traversed by walk data. -/
@[expose] def edgeSet (p : WalkData V I E) : Set E := {e | e ∈ p.edges}

@[simp, grind =] lemma edgeSet_nil : (nil u : WalkData V I E).edgeSet = ∅ := by
  ext; simp [edgeSet]

@[simp, grind =] lemma edgeSet_cons : (cons u i e j p).edgeSet = insert e p.edgeSet := by
  ext; simp [edgeSet]

@[simp, grind =] lemma mem_edgeSet : e ∈ p.edgeSet ↔ e ∈ p.edges := Iff.rfl

theorem edgeSet_finite (p : WalkData V I E) : p.edgeSet.Finite := List.finite_toSet _

/-- The set of incidences used by walk data. -/
@[expose] def incidenceSet (p : WalkData V I E) : Set I :=
  {i | ∃ ij ∈ p.incidencePairs, i = ij.1 ∨ i = ij.2}

@[simp, grind =] lemma incidenceSet_nil : (nil u : WalkData V I E).incidenceSet = ∅ := by
  ext; simp [incidenceSet]

@[simp, grind =]
lemma incidenceSet_cons : (cons u i e j p).incidenceSet = insert i (insert j p.incidenceSet) := by
  ext; grind [incidenceSet, Prod.exists]

@[simp, grind =]
lemma mem_incidenceSet : i ∈ p.incidenceSet ↔ ∃ ij ∈ p.incidencePairs, i = ij.1 ∨ i = ij.2 :=
  Iff.rfl

theorem incidenceSet_finite (p : WalkData V I E) : p.incidenceSet.Finite := by
  induction p <;> grind [Set.finite_insert]

/-- Predicate for walk data with no traversal. -/
inductive Nil : WalkData V I E → Prop
  | nil (u : V) : Nil (nil u)

/-- Predicate for walk data with at least one traversal. -/
inductive Nonempty : WalkData V I E → Prop
  | cons (u : V) (i : I) (e : E) (j : I) (p : WalkData V I E) : Nonempty (cons u i e j p)

@[simp, grind .] lemma nil_nil : (nil u : WalkData V I E).Nil := Nil.nil _

@[simp, grind .] lemma not_nil_cons : ¬ (cons u i e j p).Nil := fun h ↦ nomatch h

@[simp, grind .] lemma cons_nonempty : (cons u i e j p).Nonempty := Nonempty.cons ..

@[simp, grind .] lemma nil_not_nonempty : ¬ (nil u : WalkData V I E).Nonempty := fun h ↦ nomatch h

lemma nil_or_nonempty (p : WalkData V I E) : p.Nil ∨ p.Nonempty :=
  match p with
  | .nil _ => Or.inl nil_nil
  | .cons _ _ _ _ _ => Or.inr cons_nonempty

@[push] lemma not_nil_iff : ¬ p.Nil ↔ p.Nonempty := by
  cases p <;> simp

@[push] lemma not_nonempty_iff : ¬ p.Nonempty ↔ p.Nil := by
  cases p <;> simp

lemma Nil.first_eq_last (h : p.Nil) : p.first = p.last := by
  cases h; rfl

lemma Nonempty.exists_cons (h : p.Nonempty) : ∃ u i e j q, p = WalkData.cons u i e j q := by
  cases h with
  | cons u i e j q => exact ⟨u, i, e, j, q, rfl⟩

@[simp, grind =] lemma length_eq_zero_iff : p.length = 0 ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[simp, grind =] lemma length_pos_iff : 0 < p.length ↔ p.Nonempty := by
  cases p <;> simp

alias ⟨_, Nonempty.length_pos⟩ := length_pos_iff

instance instDecidableNil (p : WalkData V I E) : Decidable p.Nil := by
  cases p with
  | nil u => exact isTrue (Nil.nil u)
  | cons => exact isFalse not_nil_cons

instance instDecidableNonempty (p : WalkData V I E) : Decidable p.Nonempty := by
  cases p with
  | nil => exact isFalse nil_not_nonempty
  | cons => exact isTrue cons_nonempty

@[simp, grind =] theorem length_edges (p : WalkData V I E) : p.edges.length = p.length := by
  induction p <;> grind

@[simp, grind =]
theorem length_incidencePairs (p : WalkData V I E) : p.incidencePairs.length = p.length := by
  induction p <;> grind

@[simp, grind =]
theorem length_sourceIncs (p : WalkData V I E) : p.sourceIncs.length = p.length := by
  induction p <;> grind

@[simp, grind =]
theorem length_targetIncs (p : WalkData V I E) : p.targetIncs.length = p.length := by
  induction p <;> grind

@[simp, grind =]
theorem length_vertices (p : WalkData V I E) : p.vertices.length = p.length + 1 := by
  induction p <;> grind

/-- `p.IsValid G` means that each stored traversal occurs in `G`, and every stored vertex is a
vertex of `G`. -/
@[expose] def IsValid (G : Gr) : WalkData V I E → Prop
  | nil u => u ∈ V(G)
  | cons u i e j p => IsTraversal G u i e j p.first ∧ p.IsValid G

@[simp, grind =] lemma isValid_nil_iff : (nil u : WalkData V I E).IsValid G ↔ u ∈ V(G) := Iff.rfl

@[simp, grind =]
lemma isValid_cons_iff :
    (cons u i e j p).IsValid G ↔ IsTraversal G u i e j p.first ∧ p.IsValid G := Iff.rfl

@[grind →]
lemma IsValid.of_cons (h : (cons u i e j p).IsValid G) : p.IsValid G := h.2

@[grind →]
lemma IsValid.head (h : (cons u i e j p).IsValid G) : IsTraversal G u i e j p.first := h.1

@[grind →]
lemma IsValid.vertex_mem_of_mem (h : p.IsValid G) (hx : x ∈ p.vertices) : x ∈ V(G) := by
  induction p <;> grind

@[grind →]
lemma IsValid.edge_mem_of_mem (h : p.IsValid G) {e : E} (he : e ∈ p.edges) : e ∈ E(G) := by
  induction p <;> grind

@[grind →]
lemma IsValid.incidence_mem_of_mem (h : p.IsValid G) {i : I} (hi : i ∈ p.incidenceSet) :
    i ∈ I(G) := by induction p <;> grind

lemma IsValid.first_mem (h : p.IsValid G) : p.first ∈ V(G) := h.vertex_mem_of_mem p.first_mem

lemma IsValid.last_mem (h : p.IsValid G) : p.last ∈ V(G) := h.vertex_mem_of_mem p.last_mem

@[grind →]
lemma IsValid.vertexSet_subset (h : p.IsValid G) : p.vertexSet ⊆ V(G) :=
  fun _ ↦ h.vertex_mem_of_mem

@[grind →]
lemma IsValid.edgeSet_subset (h : p.IsValid G) : p.edgeSet ⊆ E(G) :=
  fun _ ↦ h.edge_mem_of_mem

@[grind →]
lemma IsValid.incidenceSet_subset (h : p.IsValid G) : p.incidenceSet ⊆ I(G) :=
  fun _ ↦ h.incidence_mem_of_mem

lemma IsValid.isChain_adj_vertices (h : p.IsValid G) : List.IsChain (Adj G) p.vertices := by
  induction p <;> grind [List.IsChain.cons_of_ne_nil]

/-- Valid walk data with the same start vertex and incidence pairs are equal: each incidence
determines its edge and endpoint. -/
lemma IsValid.ext_incidencePairs (h : p.IsValid G) (hq : q.IsValid G) (hf : p.first = q.first)
    (hinc : p.incidencePairs = q.incidencePairs) : p = q := by
  induction p generalizing q <;> cases q <;> grind

/-- Under `GraphLike` and `Loopless`, an edge has exactly one other incidence, so the edge list and
start vertex of valid walk data determine the walk. -/
lemma IsValid.ext_edges [GraphLike V I E Gr] [Loopless V I E Gr] (h : p.IsValid G)
    (hq : q.IsValid G) (hf : p.first = q.first) (he : p.edges = q.edges) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> grind
  | cons u i e j p ih =>
    cases q with
    | nil => grind
    | cons v i' e' j' q =>
      simp only [first_cons, edges_cons, List.cons.injEq] at hf he
      obtain ⟨rfl, he⟩ := he
      subst hf
      have hd : h.head.toDart = hq.head.toDart :=
        Dart.edge_source_inj <| by simp
      obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by
        simpa [Dart.ext_iff] using hd
      exact congrArg _ <| ih h.of_cons hq.of_cons (by simpa using congrArg Dart.target hd) he

/-- If a dart is determined by its ordered pair of endpoints, then the vertex list of valid walk
data determines the walk. -/
lemma IsValid.ext_vertices_of_source_target_injective (h : p.IsValid G) (hq : q.IsValid G)
    (hinj : Function.Injective fun d : Dart G ↦ (d.source, d.target))
    (hv : p.vertices = q.vertices) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> grind
  | cons u i e j p ih =>
    cases q with
    | nil => grind
    | cons v i' e' j' q =>
      simp only [vertices_cons, List.cons.injEq] at hv
      obtain ⟨rfl, hv⟩ := hv
      have hfirst : p.first = q.first := Option.some_inj.mp <| by
        simpa using congrArg List.head? hv
      have hd : h.head.toDart = hq.head.toDart :=
        hinj <| by simp only [Prod.mk.injEq]; exact ⟨by simp, by simp [hfirst]⟩
      obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by
        simpa [Dart.ext_iff] using hd
      obtain rfl : e = e' := by
        simpa using congrArg Dart.edge hd
      exact congrArg _ <| ih h.of_cons hq.of_cons hv

/-- Under `NoParallelEdge` and `Loopless`, an ordered pair of vertices determines a dart, so the
vertex list of valid walk data determines the walk. -/
lemma IsValid.ext_vertices [GraphLike V I E Gr] [NoParallelEdge V I E Gr] [Loopless V I E Gr]
    (h : p.IsValid G) (hq : q.IsValid G) (hv : p.vertices = q.vertices) : p = q :=
  h.ext_vertices_of_source_target_injective hq Dart.source_target_inj_of_undirected hv

/-- Under `NoParallelEdge` and `Directed`, there is a unique dart between an ordered pair of
vertices, so the vertex list of valid walk data determines the walk. -/
lemma IsValid.ext_vertices_of_directed [GraphLike V I E Gr] [NoParallelEdge V I E Gr]
    [Directed V I E Gr] (h : p.IsValid G) (hq : q.IsValid G) (hv : p.vertices = q.vertices) :
    p = q :=
  h.ext_vertices_of_source_target_injective hq Dart.source_target_inj_of_directed hv

/-- Extract the certified darts from valid walk data. -/
@[expose] noncomputable def IsValid.darts : ∀ (p : WalkData V I E), p.IsValid G → List (Dart G)
  | .nil _, _ => []
  | .cons _ _ _ _ p, h => h.1.toDart :: IsValid.darts p h.2

@[simp]
lemma IsValid.darts_nil (hu : u ∈ V(G)) : IsValid.darts (G := G) (.nil u) hu = [] := rfl

@[simp]
lemma IsValid.darts_cons (h : (cons u i e j p).IsValid G) :
    IsValid.darts (G := G) (cons u i e j p) h = h.1.toDart :: IsValid.darts p h.2 := rfl

@[simp] theorem IsValid.length_darts (h : p.IsValid G) : h.darts.length = p.length := by
  induction p with
  | nil => rfl
  | cons => grind [darts_cons]

theorem IsValid.map_edge_darts (h : p.IsValid G) : h.darts.map Dart.edge = p.edges := by
  induction p with
  | nil => rfl
  | cons => grind [darts_cons]

theorem IsValid.map_source_darts_append (h : p.IsValid G) :
    h.darts.map Dart.source ++ [p.last] = p.vertices := by
  induction p with
  | nil => rfl
  | cons => grind [darts_cons]

theorem IsValid.map_target_darts (h : p.IsValid G) : h.darts.map Dart.target = p.vertices.tail := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => grind [darts_cons, vertices_head p]

end WalkData

/-- A `Walk G u v` is valid `WalkData` in `G` whose first and last vertices are `u` and `v`. -/
@[expose] def Walk (G : Gr) (u v : V) : Type _ :=
  {p : WalkData V I E // p.IsValid G ∧ p.first = u ∧ p.last = v}

namespace Walk

variable {p q : Walk G u v}

/-- The underlying graph-independent data of a walk. -/
@[expose] def data (p : Walk G u v) : WalkData V I E := p.1

/-- Validity proof carried by a walk. -/
@[grind .] lemma isValid (p : Walk G u v) : p.data.IsValid G := p.2.1

/-- The first vertex of the data underlying a walk is its initial index. -/
@[grind =] lemma first_eq (p : Walk G u v) : p.data.first = u := p.2.2.1

/-- The last vertex of the data underlying a walk is its terminal index. -/
@[grind =] lemma last_eq (p : Walk G u v) : p.data.last = v := p.2.2.2

/-- The empty walk at a graph vertex. -/
@[expose] def nil (hu : u ∈ V(G)) : Walk G u u :=
  ⟨.nil u, hu, rfl, rfl⟩

/-- Prepend an explicitly certified traversal to a walk. -/
@[expose] def consRaw (i : I) (e : E) (j : I) (h : IsTraversal G u i e j v)
    (p : Walk G v w) : Walk G u w :=
  let hhead : IsTraversal G u i e j p.data.first := by
    rw [p.first_eq]
    exact h
  ⟨.cons u i e j p.data, ⟨hhead, p.isValid⟩, rfl, p.last_eq⟩

/-- Prepend a certified dart to a walk. -/
@[expose] noncomputable def cons (d : Dart G) (p : Walk G d.target w) : Walk G d.source w :=
  consRaw d.fst d.edge d.snd d.isTraversal p

/-- The one-step walk associated with a dart. -/
@[expose] noncomputable def _root_.HyperGraphLike.Dart.toWalk (d : Dart G) :
    Walk G d.source d.target := Walk.cons d (Walk.nil d.target_mem)

@[match_pattern] abbrev nil' (u : V) (hu : u ∈ V(G)) : Walk G u u := Walk.nil hu

@[match_pattern]
abbrev consRaw' (u : V) (i : I) (e : E) (j : I) (v w : V) (h : IsTraversal G u i e j v)
    (p : Walk G v w) : Walk G u w := Walk.consRaw i e j h p

@[match_pattern]
noncomputable abbrev cons' (d : Dart G) (w : V) (p : Walk G d.target w) : Walk G d.source w :=
  Walk.cons d p

@[simp, grind =] theorem data_nil (hu : u ∈ V(G)) : (nil hu).data = .nil u := rfl

@[simp, grind =] theorem first_nil (hu : u ∈ V(G)) : (nil hu).data.first = u := rfl

@[simp, grind =] theorem last_nil (hu : u ∈ V(G)) : (nil hu).data.last = u := rfl

@[simp, grind =]
theorem data_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).data = .cons u i e j p.data := rfl

@[simp, grind =]
theorem data_cons (d : Dart G) (p : Walk G d.target w) :
    (cons d p).data = .cons d.source d.fst d.edge d.snd p.data := rfl

/-- The number of darts in a walk. -/
@[expose] def length (p : Walk G u v) : ℕ := p.data.length

@[simp, grind =] theorem length_nil (hu : u ∈ V(G)) : (nil hu).length = 0 := rfl

@[simp, grind =]
theorem length_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).length = p.length + 1 := rfl

/-- The vertices visited by a walk. -/
@[expose] def vertices (p : Walk G u v) : List V := p.data.vertices

@[simp, grind =]
theorem vertices_nil (hu : u ∈ V(G)) : (nil hu).vertices = [u] := rfl

@[simp, grind =]
theorem vertices_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).vertices = u :: p.vertices := rfl

@[simp, grind =]
theorem length_vertices (p : Walk G u v) : p.vertices.length = p.length + 1 :=
  p.data.length_vertices

@[simp, grind .] theorem vertices_ne_nil (p : Walk G u v) : p.vertices ≠ [] :=
  p.data.vertices_ne_nil

@[simp, grind .] theorem start_mem_vertices (p : Walk G u v) : u ∈ p.vertices := by
  nth_rw 2 [← p.first_eq]
  exact p.data.first_mem

@[simp, grind .] theorem end_mem_vertices (p : Walk G u v) : v ∈ p.vertices := by
  nth_rw 2 [← p.last_eq]
  exact p.data.last_mem

theorem isChain_adj_vertices (p : Walk G u v) : List.IsChain (Adj G) p.vertices :=
  p.isValid.isChain_adj_vertices

@[simp, grind =]
theorem head_vertices (p : Walk G u v) : p.vertices.head p.vertices_ne_nil = u := by
  nth_rw 3 [← p.first_eq]
  exact p.data.vertices_head

@[simp, grind =]
theorem getLast_vertices (p : Walk G u v) : p.vertices.getLast p.vertices_ne_nil = v := by
  nth_rw 3 [← p.last_eq]
  exact p.data.vertices_getLast

lemma ext_vertices [GraphLike V I E Gr] [NoParallelEdge V I E Gr] [Loopless V I E Gr]
    (h : p.vertices = q.vertices) : p = q :=
  Subtype.ext <| WalkData.IsValid.ext_vertices p.isValid q.isValid h

lemma ext_vertices_of_directed [GraphLike V I E Gr] [NoParallelEdge V I E Gr] [Directed V I E Gr]
    (h : p.vertices = q.vertices) : p = q :=
  Subtype.ext <| WalkData.IsValid.ext_vertices_of_directed p.isValid q.isValid h

/-- The edges traversed by a walk. -/
@[expose] def edges (p : Walk G u v) : List E := p.data.edges

@[simp, grind =] theorem edges_nil (hu : u ∈ V(G)) : (nil hu).edges = [] := rfl

@[simp, grind =]
theorem edges_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).edges = e :: p.edges := rfl

@[simp, grind =]
theorem length_edges (p : Walk G u v) : p.edges.length = p.length := p.data.length_edges

lemma ext_edges [GraphLike V I E Gr] [Loopless V I E Gr] (h : p.edges = q.edges) : p = q :=
  Subtype.ext <| WalkData.IsValid.ext_edges p.isValid q.isValid (by grind) h

/-- The incidence pairs used by a walk. -/
@[expose] def incidencePairs (p : Walk G u v) : List (I × I) := p.data.incidencePairs

@[simp, grind =] theorem incidencePairs_nil (hu : u ∈ V(G)) : (nil hu).incidencePairs = [] := rfl

@[simp, grind =]
theorem incidencePairs_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).incidencePairs = (i, j) :: p.incidencePairs := rfl

@[simp, grind =]
theorem length_incidencePairs (p : Walk G u v) : p.incidencePairs.length = p.length :=
  p.data.length_incidencePairs

/-- Two walks are equal if they have the same sequence of incidence pairs. -/
@[ext] lemma ext (h : p.data.incidencePairs = q.data.incidencePairs) : p = q :=
  Subtype.ext <| WalkData.IsValid.ext_incidencePairs p.isValid q.isValid (by grind) h

/-- The certified darts traversed by a walk. -/
@[expose] noncomputable def darts (p : Walk G u v) : List (Dart G) := p.isValid.darts

@[simp] theorem darts_nil (hu : u ∈ V(G)) : (nil hu).darts = [] := rfl

@[simp]
theorem darts_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    (consRaw i e j h p).darts = h.toDart :: p.darts := congrArg₂ (· :: ·) rfl rfl

@[simp]
theorem length_darts (p : Walk G u v) : p.darts.length = p.length := p.isValid.length_darts

theorem map_edge_darts (p : Walk G u v) : p.darts.map Dart.edge = p.edges :=
  p.isValid.map_edge_darts

theorem map_source_darts_append (p : Walk G u v) : p.darts.map Dart.source ++ [v] = p.vertices := by
  nth_rw 2 [← p.last_eq]
  exact p.isValid.map_source_darts_append

theorem map_target_darts (p : Walk G u v) : p.darts.map Dart.target = p.vertices.tail :=
  p.isValid.map_target_darts

@[expose] def vertexSet (p : Walk G u v) : Set V := p.data.vertexSet

lemma vertexSet_subset (p : Walk G u v) : p.vertexSet ⊆ V(G) := p.isValid.vertexSet_subset

@[expose] def edgeSet (p : Walk G u v) : Set E := p.data.edgeSet

lemma edgeSet_subset (p : Walk G u v) : p.edgeSet ⊆ E(G) := p.isValid.edgeSet_subset

@[expose] def incidenceSet (p : Walk G u v) : Set I := p.data.incidenceSet

lemma incidenceSet_subset (p : Walk G u v) : p.incidenceSet ⊆ I(G) :=
  p.isValid.incidenceSet_subset

/-- Predicate for an endpoint-indexed empty walk. -/
abbrev Nil (p : Walk G u v) : Prop := p.data.Nil

/-- Predicate for an endpoint-indexed nonempty walk. -/
abbrev Nonempty (p : Walk G u v) : Prop := p.data.Nonempty

@[simp, grind .] theorem nil_nil (hu : u ∈ V(G)) : (nil hu).Nil := WalkData.nil_nil

@[simp, grind .]
theorem not_nil_consRaw (h : IsTraversal G u i e j v) (p : Walk G v w) :
    ¬ (consRaw i e j h p).Nil := WalkData.not_nil_cons

@[simp, grind =]
theorem length_eq_zero_iff (p : Walk G u v) : p.length = 0 ↔ p.Nil :=
  p.data.length_eq_zero_iff

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[simp, grind =]
theorem length_pos_iff (p : Walk G u v) : 0 < p.length ↔ p.Nonempty :=
  p.data.length_pos_iff

alias ⟨_, Nonempty.length_pos⟩ := length_pos_iff

theorem nil_or_nonempty (p : Walk G u v) : p.Nil ∨ p.Nonempty := p.data.nil_or_nonempty

theorem exists_eq_consRaw_of_nonempty (h : p.Nonempty) :
    ∃ (x : V) (i : I) (e : E) (j : I) (q : Walk G x v),
      ∃ ht : IsTraversal G u i e j x, p = consRaw i e j ht q := by
  obtain ⟨u', i, e, j, q, hq⟩ := WalkData.Nonempty.exists_cons h
  obtain rfl : u' = u := by grind [p.first_eq]
  obtain rfl : q.last = v := by grind [p.last_eq]
  obtain ⟨htrav, hqvalid⟩ := hq ▸ p.isValid
  exact ⟨q.first, i, e, j, ⟨q, hqvalid, rfl, rfl⟩, htrav, Subtype.ext hq⟩

theorem exists_eq_consRaw_of_ne (huv : u ≠ v) (p : Walk G u v) :
    ∃ (x : V) (i : I) (e : E) (j : I) (q : Walk G x v),
      ∃ ht : IsTraversal G u i e j x, p = consRaw i e j ht q := by
  refine exists_eq_consRaw_of_nonempty ?_
  by_contra! h
  grind [h.first_eq_last]

end Walk

end HyperGraphLike
