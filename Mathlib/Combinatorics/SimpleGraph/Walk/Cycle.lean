/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Circuit
import Mathlib.Combinatorics.SimpleGraph.Walk.Path
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *cycle* is a circuit whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsCycle`.

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
cycles, bridge edges
-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

namespace Walk

variable {G} {u v w : V}

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends IsCircuit p where
  support_nodup : p.support.tail.Nodup

-- Porting note: used to use `extends to_circuit : is_circuit p` in structure
protected lemma IsCycle.isCircuit {p : Walk G u u} (h : IsCycle p) : IsCircuit p := h.toIsCircuit

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

section WalkDecomp

variable [DecidableEq V]

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


end WalkDecomp

end Walk

theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.cons_isTrail_iff, he]

/-! ### Mapping paths -/

namespace Walk

variable {G G' G''}
variable (f : G →g G') {u v : V} (p : G.Walk u v)
variable {p f}

theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, map_isTrail_iff_of_injective hinj, Ne, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]

alias ⟨_, IsCycle.map⟩ := map_isCycle_iff_of_injective

@[simp]
theorem mapLe_isCycle {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := mapLe_isCycle

end Walk

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {u v : V} {H : SimpleGraph V}
variable {p : G.Walk u v}


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

protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _

end Walk

/-! ### Bridge edges -/

section BridgeEdges

variable {G}

theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_delete_edges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply cons_isCycle
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

end BridgeEdges

end SimpleGraph
