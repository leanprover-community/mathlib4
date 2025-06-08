/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`, and `SimpleGraph.Walk.IsCycle`.

* `SimpleGraph.Path`

* `SimpleGraph.Path.map` for the induced map on paths,
  given an (injective) graph homomorphism.

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
trails, paths, circuits, cycles, bridge edges
-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

namespace Walk

variable {G} {u v w : V}

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

/-- A *path* is a walk with no repeating vertices.
Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) : Prop extends IsTrail p where
  support_nodup : p.support.Nodup

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsPath.isTrail {p : Walk G u v} (h : IsPath p) : IsTrail p := h.toIsTrail

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends IsTrail p where
  ne_nil : p ≠ nil

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsCircuit.isTrail {p : Walk G u u} (h : IsCircuit p) : IsTrail p := h.toIsTrail

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends IsCircuit p where
  support_nodup : p.support.tail.Nodup

-- Porting note: used to use `extends to_circuit : is_circuit p` in structure
protected lemma IsCycle.isCircuit {p : Walk G u u} (h : IsCycle p) : IsCircuit p := h.toIsCircuit

@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

@[simp]
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl

lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl

lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]

@[simp]
theorem cons_isTrail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]

theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h

@[simp]
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try rw [reverse_reverse]

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩

theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

theorem IsTrail.length_le_card_edgeFinset [Fintype G.edgeSet] {u v : V}
    {w : G.Walk u v} (h : w.IsTrail) : w.length ≤ G.edgeFinset.card := by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges ⊆ G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using h
  exact Finset.card_le_card this

theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by constructor <;> simp

theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [isPath_def]

@[simp]
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp +contextual [isPath_def]

protected lemma IsPath.cons {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
theorem isPath_iff_eq_nil {u : V} (p : G.Walk u u) : p.IsPath ↔ p = nil := by
  cases p <;> simp [IsPath.nil]

theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h

@[simp]
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse; simp

theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left

theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left

lemma IsPath.of_adj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : h.toWalk.IsPath := by
  aesop

@[simp]
theorem IsCycle.not_of_nil {u : V} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl

lemma IsCycle.ne_bot : ∀ {p : G.Walk u u}, p.IsCycle → G ≠ ⊥
  | nil, hp => by cases hp.ne_nil rfl
  | cons h _, hp => by rintro rfl; exact h

lemma IsCycle.three_le_length {v : V} {p : G.Walk v v} (hp : p.IsCycle) : 3 ≤ p.length := by
  have ⟨⟨hp, hp'⟩, _⟩ := hp
  match p with
  | .nil => simp at hp'
  | .cons h .nil => simp at h
  | .cons _ (.cons _ .nil) => simp at hp
  | .cons _ (.cons _ (.cons _ _)) => simp_rw [SimpleGraph.Walk.length_cons]; omega

lemma not_nil_of_isCycle_cons {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle) :
    ¬ p.Nil := by
  have := Walk.length_cons _ _ ▸ Walk.IsCycle.three_le_length hc
  rw [Walk.not_nil_iff_lt_length]
  omega

theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup
  tauto

protected lemma IsCycle.reverse {p : G.Walk u u} (h : p.IsCycle) : p.reverse.IsCycle := by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' ↦ h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]
lemma isCycle_reverse {p : G.Walk u u} : p.reverse.IsCycle ↔ p.IsCycle where
  mp h := by simpa using h.reverse
  mpr := .reverse

lemma IsCycle.isPath_of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : ¬ p.Nil)
    (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [tail_support_append, List.nodup_append] at this
  rw [isPath_def, support_eq_cons, List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩

lemma IsCycle.isPath_of_append_left {p : G.Walk u v} {q : G.Walk v u} (h : ¬ q.Nil)
    (hcyc : (p.append q).IsCycle) : p.IsPath :=
  p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))

lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) : p.tail.IsPath := by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]

/-! ### About paths -/

instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance

theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card

lemma IsPath.getVert_injOn {p : G.Walk u v} (hp : p.IsPath) :
    Set.InjOn p.getVert {i | i ≤ p.length} := by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => aesop
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_setOf_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · aesop
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
      have hvp : v ∉ p.support := by aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(m - 1), ⟨hnm.symm, by omega⟩⟩)).elim
    · simp only [hm0, Walk.getVert_cons p h hn0] at hnm
      have hvp : v ∉ p.support := by aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(n - 1), ⟨hnm, by omega⟩⟩)).elim
    · simp only [Walk.getVert_cons _ _ hn0, Walk.getVert_cons _ _ hm0] at hnm
      have := ihp hp.of_cons (by omega : (n - 1) ≤ p.length)
        (by omega : (m - 1) ≤ p.length) hnm
      omega

lemma IsPath.getVert_eq_start_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 := by
  refine ⟨?_, by aesop⟩
  intro h
  by_cases hi : i = 0
  · exact hi
  · apply hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by rw [Set.mem_setOf]; omega)
    simp [h]

lemma IsPath.getVert_eq_end_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = w ↔ i = p.length := by
  have := hp.reverse.getVert_eq_start_iff (by omega : p.reverse.length - i ≤ p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by omega] at this
  rw [this]
  omega

lemma IsPath.getVert_injOn_iff (p : G.Walk u v) : Set.InjOn p.getVert {i | i ≤ p.length} ↔
    p.IsPath := by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_setOf_eq] at hn hm
      have := hinj (by rw [length_cons]; omega : n + 1 ≤ (q.cons h).length)
          (by rw [length_cons]; omega : m + 1 ≤ (q.cons h).length)
          (by simpa [getVert_cons] using hnm)
      omega), fun h' => ?_⟩
    obtain ⟨n, ⟨hn, hnl⟩⟩ := mem_support_iff_exists_getVert.mp h'
    have := hinj (by rw [length_cons]; omega : (n + 1) ≤ (q.cons h).length)
      (by omega : 0 ≤ (q.cons h).length) (show (q.cons h).getVert (n + 1) = (q.cons h).getVert 0
        from by rwa [getVert_cons _ _ (by omega : n + 1 ≠ 0), getVert_zero])
    omega

/-! ### About cycles -/

-- TODO: These results could possibly be less laborious with a periodic function getCycleVert
lemma IsCycle.getVert_injOn {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.length} := by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc)), Set.mem_setOf] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
      (by omega : n - 1 ≤ p.tail.length) (by omega : m - 1 ≤ p.tail.length)
      (by simp_all [SimpleGraph.Walk.getVert_tail, show n - 1 + 1 = n by omega,
          show m - 1 + 1 = m by omega])
  omega

lemma IsCycle.getVert_injOn' {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i |  i ≤ p.length - 1} := by
  intro n hn m hm hnm
  simp only [Walk.length_reverse, Set.mem_setOf_eq, Nat.sub_le, and_true] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_setOf_eq]; omega)
    (by simp only [Walk.length_reverse, Set.mem_setOf_eq]; omega)
    (by simp [Walk.getVert_reverse, show p.length - (p.length - n) = n by omega, hnm,
      show p.length - (p.length - m) = m by omega])
  omega

lemma IsCycle.snd_ne_penultimate {p : G.Walk u u} (hp : p.IsCycle) : p.snd ≠ p.penultimate := by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; omega) (by simp; omega) at h
  omega

lemma IsCycle.getVert_endpoint_iff {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle) (hl : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 ∨ i = p.length := by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) (h.symm ▸ (Walk.getVert_length p).symm)

lemma IsCycle.getVert_sub_one_ne_getVert_add_one {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i ≤ p.length) : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  have hl := hpc.three_le_length
  by_cases hi' : i ≥ p.length - 1
  · intro h'
    rw [p.getVert_of_length_le (by omega : p.length ≤ i + 1),
      hpc.getVert_endpoint_iff (by omega)] at h'
    omega
  intro h'
  have := hpc.getVert_injOn' (by simp only [Set.mem_setOf_eq, Nat.sub_le_iff_le_add]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) h'
  omega

@[deprecated (since := "2025-04-27")]
alias IsCycle.getVert_sub_one_neq_getVert_add_one := IsCycle.getVert_sub_one_ne_getVert_add_one

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

protected theorem IsPath.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail := by
  rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]
  exact hc.edges_nodup

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit := by
  refine ⟨hc.isTrail.rotate _, ?_⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simp at hn'

protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.support) :
    (c.rotate h).IsCycle := by
  refine ⟨hc.isCircuit.rotate _, ?_⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup

lemma IsCycle.isPath_takeUntil {c : G.Walk v v} (hc : c.IsCycle) (h : w ∈ c.support) :
    (c.takeUntil w h).IsPath := by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse, ← take_spec c h, reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))

/-- Taking a strict initial segment of a path removes the end vertex from the support. -/
lemma endpoint_notMem_support_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support)
    (h : v ≠ w) : v ∉ (p.takeUntil w hw).support := by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_setOf]; omega) (by simp)
    (hn.symm ▸ p.getVert_length.symm)
  omega

@[deprecated (since := "2025-05-23")]
alias endpoint_not_mem_support_takeUntil := endpoint_notMem_support_takeUntil

end WalkDecomp

end Walk

/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }

namespace Path

variable {G G'}

@[simp]
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property

@[simp]
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩

theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    s(u, v) ∈ (singleton h : G.Walk u v).edges := by simp [singleton]

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩

theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw

theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property

theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h

theorem notMem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} :
    e ∉ (p : G.Walk v v).edges := by simp [p.loop_eq]

@[deprecated (since := "2025-05-23")] alias not_mem_edges_of_loop := notMem_edges_of_loop

theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.cons_isTrail_iff, he]

end Path


/-! ### Walks to paths -/

namespace Walk

variable {G} [DecidableEq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]
theorem bypass_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl

theorem bypass_isPath {u v : V} (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [bypass]
    split_ifs
    · trans
      · apply length_dropUntil_le
      rw [length_cons]
      omega
    · rw [length_cons, length_cons]
      exact Nat.add_le_add_right ih 1

lemma bypass_eq_self_of_length_le {u v : V} (p : G.Walk u v) (h : p.length ≤ p.bypass.length) :
    p.bypass = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.bypass]
    split_ifs with hb
    · exfalso
      simp only [hb, Walk.bypass, Walk.length_cons, dif_pos] at h
      apply Nat.not_succ_le_self p.length
      calc p.length + 1
        _ ≤ (p.bypass.dropUntil _ _).length := h
        _ ≤ p.bypass.length := Walk.length_dropUntil_le p.bypass hb
        _ ≤ p.length := Walk.length_bypass_le _
    · simp only [hb, Walk.bypass, Walk.length_cons, not_false_iff, dif_neg,
        Nat.add_le_add_iff_right] at h
      rw [ih h]

/-- Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩

theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.support ⊆ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (support_dropUntil_subset _ _)
      apply List.subset_cons_of_subset
      assumption
    · rw [support_cons]
      apply List.cons_subset_cons
      assumption

theorem support_toPath_subset {u v : V} (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  support_bypass_subset _

theorem darts_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.darts ⊆ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (darts_dropUntil_subset _ _)
      apply List.subset_cons_of_subset _ ih
    · rw [darts_cons]
      exact List.cons_subset_cons _ ih

theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subset _ p.darts_bypass_subset

theorem darts_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _

theorem edges_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G' G''}
variable (f : G →g G') {u v : V} (p : G.Walk u v)
variable {p f}

theorem map_isPath_of_injective (hinj : Function.Injective f) (hp : p.IsPath) :
    (p.map f).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [Walk.cons_isPath_iff] at hp
    simp only [map_cons, cons_isPath_iff, ih hp.1, support_map, List.mem_map, not_exists, not_and,
      true_and]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx

protected theorem IsPath.of_map {f : G →g G'} (hp : (p.map f).IsPath) : p.IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, Walk.cons_isPath_iff, support_map] at hp
    rw [Walk.cons_isPath_iff]
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨ih hp1, ?_⟩
    contrapose! hp2
    exact List.mem_map_of_mem hp2

theorem map_isPath_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_isPath_of_injective hinj⟩

theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, cons_isTrail_iff, ih, cons_isTrail_iff]
    apply and_congr_right'
    rw [← Sym2.map_pair_eq, edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]

alias ⟨_, map_isTrail_of_injective⟩ := map_isTrail_iff_of_injective

theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, map_isTrail_iff_of_injective hinj, Ne, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]

alias ⟨_, IsCycle.map⟩ := map_isCycle_iff_of_injective

@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := mapLe_isTrail

@[simp]
theorem mapLe_isPath {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  map_isPath_iff_of_injective Function.injective_id

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := mapLe_isPath

@[simp]
theorem mapLe_isCycle {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := mapLe_isCycle

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_isPath_of_injective hinj p.2⟩

theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.coe_mk, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p

theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.injective u v

end Path

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {u v : V} {H : SimpleGraph V}
variable {p : G.Walk u v}

protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _ ] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩

protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.find?, List.mem_cons, forall_eq_or_imp, mem_edgeSet] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩

end Walk

/-! ## Deleting edges -/

namespace Walk

variable {v w : V}

protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _

protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _

@[simp]
theorem toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl

end Walk

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

variable {G}

theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v) :=
  not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp

protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath

protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩

protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable

@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩

protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _

@[symm]
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩

theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

theorem reachable_iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩

protected theorem Reachable.map {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩

@[mono]
protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
    (h : G ≤ G') (Guv : G.Reachable u v) : G'.Reachable u v := Guv.map (.ofLE h)

theorem Reachable.exists_isPath {u v} (hr : G.Reachable u v) : ∃ p : G.Walk u v, p.IsPath := by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩

theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]

lemma Reachable.mem_subgraphVerts {u v} {H : G.Subgraph} (hr : G.Reachable u v)
    (h : ∀ v ∈ H.verts, ∀ w, G.Adj v w → H.Adj v w)
    (hu : u ∈ H.verts) : v ∈ H.verts := by
  let rec aux {v' : V} (hv' : v' ∈ H.verts) (p : G.Walk v' v) : v ∈ H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    omega
  }
  exact aux hu hr.some

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- Distinct vertices are not reachable in the empty graph. -/
@[simp]
lemma reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v :=
  ⟨fun h ↦ h.elim fun p ↦ match p with | .nil => rfl, fun h ↦ h ▸ .rfl⟩

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _

@[mono]
protected lemma Preconnected.mono  {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

lemma bot_preconnected_iff_subsingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa [subsingleton_iff, ← reachable_bot] using h⟩
  contrapose h
  simp [nontrivial_iff.mp <| not_subsingleton_iff_nontrivial.mp h, Preconnected, reachable_bot, h]

lemma bot_preconnected [Subsingleton V] : (⊥ : SimpleGraph V).Preconnected :=
  bot_preconnected_iff_subsingleton.mpr ‹_›

lemma bot_not_preconnected [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected :=
  bot_preconnected_iff_subsingleton.not.mpr <| not_subsingleton_iff_nontrivial.mpr ‹_›

lemma top_preconnected : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

lemma Preconnected.support_eq_univ [Nontrivial V] {G : SimpleGraph V}
    (h : G.Preconnected) : G.support = Set.univ := by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => use w

lemma adj_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
    (hx : x ∈ p.support) : ∃y ∈ p.support, G.Adj x y := by
  induction p with
  | nil =>
    exact (hp Walk.Nil.nil).elim
  | @cons u v w h p ih =>
    cases List.mem_cons.mp hx with
    | inl hxu =>
      rw [hxu]
      exact ⟨v, ⟨((Walk.cons h p).mem_support_iff).mpr (Or.inr p.start_mem_support), h⟩⟩
    | inr hxp =>
      cases Decidable.em p.Nil with
      | inl hnil =>
        rw [Walk.nil_iff_support_eq.mp hnil] at hxp
        rw [show (x = v) by simp_all]
        exact ⟨u, ⟨(Walk.cons h p).start_mem_support, G.adj_symm h⟩⟩
      | inr hnotnil =>
        obtain ⟨y, hy⟩ := ih hnotnil hxp
        refine ⟨y, ⟨?_, hy.right⟩⟩
        rw [Walk.mem_support_iff]
        simp only [Walk.support_cons, List.tail_cons]
        exact Or.inr hy.left

lemma mem_support_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
    {w : V} (hw : w ∈ p.support) : w ∈ G.support := by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩

lemma mem_support_of_reachable {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (h : G.Reachable u v) :
    u ∈ G.support := by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support

theorem Preconnected.exists_isPath {G : SimpleGraph V} (h : G.Preconnected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]

lemma connected_iff_exists_forall_reachable : G.Connected ↔ ∃ v, ∀ w, G.Reachable v w := by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v := ⟨fun h => h.preconnected⟩

theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[mono]
protected lemma Connected.mono {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.Connected) : G'.Connected where
  preconnected := hG.preconnected.mono h
  nonempty := hG.nonempty

theorem Connected.exists_isPath {G : SimpleGraph V} (h : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

lemma bot_not_connected [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected := by
  simp [bot_not_preconnected, connected_iff, ‹_›]

lemma top_connected [Nonempty V] : (⊤ : SimpleGraph V).Connected where
  preconnected := top_preconnected

theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

/-- The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent := Quot G.Reachable

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v

variable {G G' G''}

namespace ConnectedComponent

@[simps]
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩

instance isEmpty [IsEmpty V] : IsEmpty (ConnectedComponent G) := by
  by_contra! hc
  rw [@not_isEmpty_iff] at hc
  obtain ⟨v, _⟩ := (Classical.inhabited_of_nonempty hc).default.exists_rep
  exact IsEmpty.false v

@[elab_as_elim]
protected theorem ind {β : G.ConnectedComponent → Prop}
    (h : ∀ v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c

@[elab_as_elim]
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h

protected theorem sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound

protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _

@[simp]
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _

theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
protected theorem lift_mk {β : Sort*} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl

protected theorem «exists» {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.exists

protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.forall

theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
def recOn
    {motive : G.ConnectedComponent → Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) → motive (G.connectedComponentMk v))
    (h : ∀ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl

@[simp]
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := C.ind (fun _ => rfl)

@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  C.ind (fun _ => rfl)

variable {φ : G ≃g G'} {v : V} {v' : V'}

@[simp]
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

end ConnectedComponent

namespace Iso

/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

@[simp]
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl

@[simp]
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl

@[simp]
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl

end Iso

namespace ConnectedComponent

/-- The set of vertices in a connected component of a graph. -/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }

@[ext]
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq]
  intro v w h
  rw [reachable_comm, h]

@[simp]
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff

instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective' := ConnectedComponent.supp_injective

@[simp]
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl

lemma mem_supp_congr_adj {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) :
    v ∈ c.supp ↔ w ∈ c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj

theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl

theorem nonempty_supp (C : G.ConnectedComponent) : C.supp.Nonempty := C.exists_rep

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext_val (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext_val (φ.toEquiv.right_inv ↑v)

lemma mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
    (hv : v ∈ (↑) '' (c : Set H.verts)) (hw : w ∈ H.verts)
    (hadj : H.Adj v w) : w ∈ (↑) '' (c : Set H.verts) := by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
  exact ⟨connectedComponentMk_eq_of_adj <| Subgraph.Adj.coe <| h.2 ▸ hadj.symm, rfl⟩

lemma eq_of_common_vertex {v : V} {c c' : ConnectedComponent G} (hc : v ∈ c.supp)
    (hc' : v ∈ c'.supp) : c = c' := by
  simp only [mem_supp_iff] at *
  rw [← hc, ← hc']

lemma connectedComponentMk_supp_subset_supp {G'} {v : V} (h : G ≤ G') (c' : G'.ConnectedComponent)
    (hc' : v ∈ c'.supp) : (G.connectedComponentMk v).supp ⊆ c'.supp := by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

lemma biUnion_supp_eq_supp {G G' : SimpleGraph V} (h : G ≤ G') (c' : ConnectedComponent G') :
    ⋃ (c : ConnectedComponent G) (_ : c.supp ⊆ c'.supp), c.supp = c'.supp := by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ ↦ hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]

lemma top_supp_eq_univ (c : ConnectedComponent (⊤ : SimpleGraph V)) :
    c.supp = (Set.univ : Set V) := by
  have ⟨w, hw⟩ := c.exists_rep
  ext v
  simp only [Set.mem_univ, iff_true, mem_supp_iff, ← hw]
  apply ConnectedComponent.sound
  exact (@top_connected V (Nonempty.intro v)).preconnected v w

lemma reachable_of_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) : G.Reachable u v := by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)

lemma mem_supp_of_adj_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hadj : G.Adj u v) : v ∈ C.supp := by
  have hC : G.connectedComponentMk u = G.connectedComponentMk v :=
    connectedComponentMk_eq_of_adj hadj
  rw [hu] at hC
  exact hC.symm

/--
Given a connected component `C` of a simple graph `G`, produce the induced graph on `C`.
The declaration `connected_toSimpleGraph` shows it is connected, and `toSimpleGraph_hom`
provides the homomorphism back to `G`.
-/
def toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) : SimpleGraph C := G.induce C.supp

/-- Homomorphism from a connected component graph to the original graph. -/
def toSimpleGraph_hom {G : SimpleGraph V} (C : G.ConnectedComponent) : C.toSimpleGraph →g G where
  toFun u := u.val
  map_rel' := id

lemma toSimpleGraph_hom_apply {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph_hom u = u.val := rfl

lemma toSimpleGraph_adj {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u ∈ C)
    (hv : v ∈ C) : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v := by
  simp [toSimpleGraph]

lemma adj_spanningCoe_toSimpleGraph {v w : V} (C : G.ConnectedComponent) :
    C.toSimpleGraph.spanningCoe.Adj v w ↔ v ∈ C.supp ∧ G.Adj v w := by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, h₂, h₃⟩ := h
    subst h₂ h₃
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
    intro h hadj
    exact ⟨v, h, w, hadj, rfl, (C.mem_supp_congr_adj hadj).mp h, rfl⟩

@[deprecated (since := "2025-05-08")]
alias adj_spanningCoe_induce_supp := adj_spanningCoe_toSimpleGraph

/-- Get the walk between two vertices in a connected component from a walk in the original graph. -/
private def walk_toSimpleGraph' {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (p : G.Walk u v) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph' hw hv p)

@[deprecated (since := "2025-05-08")] alias reachable_induce_supp := walk_toSimpleGraph'

/-- There is a walk between every pair of vertices in a connected component. -/
noncomputable def walk_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ :=
  C.walk_toSimpleGraph' hu hv (C.reachable_of_mem_supp hu hv).some

lemma reachable_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C.toSimpleGraph.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Walk.reachable (C.walk_toSimpleGraph hu hv)

lemma connected_toSimpleGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where
  preconnected := by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩

@[deprecated (since := "2025-05-08")] alias connected_induce_supp := connected_toSimpleGraph

end ConnectedComponent

-- TODO: Extract as lemma about general equivalence relation
lemma pairwise_disjoint_supp_connectedComponent (G : SimpleGraph V) :
    Pairwise fun c c' : ConnectedComponent G ↦ Disjoint c.supp c'.supp := by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

-- TODO: Extract as lemma about general equivalence relation
lemma iUnion_connectedComponentSupp (G : SimpleGraph V) :
    ⋃ c : G.ConnectedComponent, c.supp = Set.univ := by
  refine Set.eq_univ_of_forall fun v ↦ ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩

theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v

/-! ### Bridge edges -/

section BridgeEdges

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, by simp [reachable_comm]⟩ e

theorem isBridge_iff {u v : V} :
    G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v := Iff.rfl

theorem reachable_delete_edges_iff_exists_walk {v w v' w' : V} :
    (G \ fromEdgeSet {s(v, w)}).Reachable v' w' ↔ ∃ p : G.Walk v' w', s(v, w) ∉ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩

theorem isBridge_iff_adj_and_forall_walk_mem_edges {v w : V} :
    G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v, w) ∈ p.edges := by
  rw [isBridge_iff, and_congr_right']
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not]

theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : ∀ p : G.Walk v w, s(v, w) ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse, List.mem_reverse] at hpq'
  rw [Walk.isTrail_def, this, Walk.edges_append, Walk.edges_append, List.nodup_append_comm,
    ← List.append_assoc, ← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'

theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_delete_edges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset p h)
    · simp only [Sym2.eq_swap, Walk.edges_cons, List.mem_cons, eq_self_iff_true, true_or]
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : ∀ p : G.Walk w v, s(w, v) ∈ p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(Walk.rotate_edges c hvc).mem_iff, Sym2.eq_swap]

theorem isBridge_iff_adj_and_forall_cycle_notMem {v w : V} : G.IsBridge s(v, w) ↔
    G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges := by
  rw [isBridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and]

@[deprecated (since := "2025-05-23")]
alias isBridge_iff_adj_and_forall_cycle_not_mem := isBridge_iff_adj_and_forall_cycle_notMem

theorem isBridge_iff_mem_and_forall_cycle_notMem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun _ _ => isBridge_iff_adj_and_forall_cycle_notMem) e

@[deprecated (since := "2025-05-23")]
alias isBridge_iff_mem_and_forall_cycle_not_mem := isBridge_iff_mem_and_forall_cycle_notMem

/-- Deleting a non-bridge edge from a connected graph preserves connectedness. -/
lemma Connected.connected_delete_edge_of_not_isBridge (hG : G.Connected) {x y : V}
    (h : ¬ G.IsBridge s(x, y)) : (G.deleteEdges {s(x, y)}).Connected := by
  classical
  simp only [isBridge_iff, not_and, not_not] at h
  obtain hxy | hxy := em' <| G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w ↦ ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
  obtain heP | heP := em' <| s(x,y) ∈ P.edges
  · exact ⟨(P.toDeleteEdges {s(x,y)} (by aesop)).reverse⟩
  have hyP := P.snd_mem_support_of_mem_edges heP
  let P₁ := P.takeUntil y hyP
  have hxP₁ := Walk.endpoint_notMem_support_takeUntil hP hyP hxy.ne
  have heP₁ : s(x,y) ∉ P₁.edges := fun h ↦ hxP₁ <| P₁.fst_mem_support_of_mem_edges h
  exact (h hxy).trans (Reachable.symm ⟨P₁.toDeleteEdges {s(x,y)} (by aesop)⟩)

end BridgeEdges

end SimpleGraph
