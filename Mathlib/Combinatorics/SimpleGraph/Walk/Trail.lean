/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *trail* is a walk whose edges each appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail`

## Tags
trails
-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

namespace Walk

variable {G} {u v w : V}

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl

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

section WalkDecomp

variable [DecidableEq V]

protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail := by
  rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]
  exact hc.edges_nodup


end WalkDecomp

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G' G''}
variable (f : G →g G') {u v : V} (p : G.Walk u v)
variable {p f}

theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, cons_isTrail_iff, ih, cons_isTrail_iff]
    apply and_congr_right'
    rw [← Sym2.map_pair_eq, edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]

alias ⟨_, map_isTrail_of_injective⟩ := map_isTrail_iff_of_injective

@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := mapLe_isTrail

end Walk
