/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart

/-!
# Walks

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)
* `SimpleGraph.Walk.Nil`: A predicate for the empty walk
* `SimpleGraph.Walk.length`: The length of a walk
* `SimpleGraph.Walk.support`: The list of vertices a walk visits in order
* `SimpleGraph.Walk.darts`: The list of darts a walk visits in order
* `SimpleGraph.Walk.edges`: The list of edges a walk visits in order
* `SimpleGraph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

universe u
variable {V : Type u} (G : SimpleGraph V) {u v w : V}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : G.Walk u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p

theorem exists_eq_cons_of_ne {u v : V} (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (h : G.Adj u w) (p' : G.Walk w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero {u v : V} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
  | nil, _ => rfl

theorem adj_of_length_eq_one {u v : V} : ∀ {p : G.Walk u v}, p.length = 1 → G.Adj u v
  | cons h nil, _ => h

@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
lemma exists_length_eq_one_iff {u v : V} : (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun h ↦ ⟨h.toWalk, by simp⟩⟩
  induction p with
  | nil => simp at hp
  | cons h p' =>
    simp only [Walk.length_cons, add_eq_right] at hp
    exact (p'.eq_of_length_eq_zero hp) ▸ h

@[simp]
theorem length_eq_zero_iff {u : V} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge

@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] := rfl

@[simp, grind =]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl

@[simp]
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp

@[simp]
theorem head_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.head (by simp) = a := by cases p <;> simp

@[simp]
theorem getLast_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.getLast (by simp) = b := by
  induction p <;> simp [*]

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩

theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

theorem support_subset_support_cons {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support ⊆ (p.cons hadj).support := by
  simp

theorem coe_support {u v : V} (p : G.Walk u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl

theorem isChain_adj_cons_support {u v w : V} (h : G.Adj u v) :
    ∀ (p : G.Walk v w), List.IsChain G.Adj (u :: p.support)
  | nil => .cons_cons h (.singleton _)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)

@[deprecated (since := "2025-09-24")] alias chain_adj_support := isChain_adj_cons_support

theorem isChain_adj_support {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.Adj p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

@[deprecated (since := "2025-09-24")] alias chain'_adj_support := isChain_adj_support

theorem isChain_dartAdj_cons_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.IsChain G.DartAdj (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

theorem isChain_dartAdj_darts {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.DartAdj p.darts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_darts (by rfl) p

@[deprecated (since := "2025-09-24")] alias chain_dartAdj_darts := isChain_dartAdj_cons_darts
@[deprecated (since := "2025-09-24")] alias chain'_dartAdj_darts := isChain_dartAdj_darts

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edgeSet {u v : V} :
    ∀ (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'
    next h' => exact edges_subset_edgeSet p' h'

theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  p.edges_subset_edgeSet h

@[simp]
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] := rfl

@[simp]
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp [*]

theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

theorem map_fst_darts_append {u v : V} (p : G.Walk u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp [*]

theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)

@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] := rfl

@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = s(u, v) :: p.edges := rfl

@[simp, grind =]
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp, grind =]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]

@[simp]
theorem fst_darts_getElem {p : G.Walk u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].fst = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_darts]

@[simp]
theorem snd_darts_getElem {p : G.Walk u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].snd = p.support.tail[i]'(by grind) := by
  grind [map_snd_darts]

theorem mem_darts_iff_infix_support {u' v'} {p : G.Walk u v} (h : G.Adj u' v') :
    ⟨⟨u', v'⟩, h⟩ ∈ p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert p.darts.getElem_mem (n := i) (by grind)
      <;> grind [fst_darts_getElem, snd_darts_getElem]

theorem mem_darts_iff_fst_snd_infix_support {p : G.Walk u v} {d : G.Dart} :
    d ∈ p.darts ↔ [d.fst, d.snd] <:+: p.support :=
  mem_darts_iff_infix_support ..

theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    ∀ (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl rfl
    · exact .inr (dart_fst_mem_support_of_mem_darts _ hd)

theorem mem_support_iff_exists_mem_edges {u v w : V} {p : G.Walk u v} :
    w ∈ p.support ↔ w = v ∨ ∃ e ∈ p.edges, w ∈ e := by
  induction p <;> aesop

theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

theorem edges_eq_zipWith_support {u v : V} {p : G.Walk u v} :
    p.edges = List.zipWith (s(·, ·)) p.support p.support.tail := by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

theorem edges_injective {u v : V} : Function.Injective (Walk.edges : G.Walk u v → List (Sym2 V))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    have h₃ : u ≠ v' := by rintro rfl; exact G.loopless _ h₂
    obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges := by simpa [h₁, h₃] using h
    rw [edges_injective h₃]

theorem darts_injective {u v : V} : Function.Injective (Walk.darts : G.Walk u v → List G.Dart) :=
  edges_injective.of_comp

/-- The `Set` of edges of a walk. -/
def edgeSet {u v : V} (p : G.Walk u v) : Set (Sym2 V) := {e | e ∈ p.edges}

@[simp]
lemma mem_edgeSet {u v : V} {p : G.Walk u v} {e : Sym2 V} : e ∈ p.edgeSet ↔ e ∈ p.edges := Iff.rfl

@[simp]
lemma edgeSet_nil (u : V) : (nil : G.Walk u u).edgeSet = ∅ := by ext; simp

@[simp]
theorem edgeSet_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edgeSet = insert s(u, v) p.edgeSet := by ext; simp

theorem coe_edges_toFinset [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
  simp [edgeSet]

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = G.Walk.nil` typechecks
only if `p` has defeq endpoints. -/
inductive Nil : {v w : V} → G.Walk v w → Prop
  | nil {u : V} : Nil (nil : G.Walk u u)

@[simp, grind .] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : G.Adj u v} {p : G.Walk v w} : ¬ (cons h p).Nil := nofun

instance (p : G.Walk v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl

lemma not_nil_of_ne {p : G.Walk v w} : v ≠ w → ¬ p.Nil := mt Nil.eq

lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp]
lemma darts_eq_nil {p : G.Walk v w} : p.darts = [] ↔ p.Nil := by
  cases p <;> simp

@[simp]
lemma edges_eq_nil {p : G.Walk v w} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff_lt_length {p : G.Walk v w} : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

lemma not_nil_iff {p : G.Walk v w} :
    ¬ p.Nil ↔ ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : G.Walk v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : G.Walk u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) :
    @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by rfl

theorem end_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h

theorem mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil) :
    w ∈ p.support ↔ ∃ e ∈ p.edges, w ∈ e := by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x _
    by_cases h : x ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨_, a⟩, List.Mem.head _, uS, h⟩

end Walk

end SimpleGraph
