/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Parity

#align_import combinatorics.simple_graph.degree_sum from "leanprover-community/mathlib"@"90659cbe25e59ec302e2fb92b00e9732160cc620"

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `SimpleGraph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `SimpleGraph.even_card_odd_degree_vertices` is the handshaking lemma.
- `SimpleGraph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/


open Finset

open BigOperators

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

-- Porting note: Changed to `Fintype (Sym2 V)` to match Combinatorics.SimpleGraph.Basic
variable [Fintype (Sym2 V)]

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  -- ⊢ d ∈ filter (fun d => d.fst = v) univ ↔ d ∈ image (dartOfNeighborSet G v) univ
  simp only [mem_image, true_and_iff, mem_filter, SetCoe.exists, mem_univ, exists_prop_of_true]
  -- ⊢ d.fst = v ↔ ∃ x h, dartOfNeighborSet G v { val := x, property := h } = d
  constructor
  -- ⊢ d.fst = v → ∃ x h, dartOfNeighborSet G v { val := x, property := h } = d
  · rintro rfl
    -- ⊢ ∃ x h, dartOfNeighborSet G d.fst { val := x, property := h } = d
    exact ⟨_, d.is_adj, by ext <;> rfl⟩
    -- 🎉 no goals
  · rintro ⟨e, he, rfl⟩
    -- ⊢ (dartOfNeighborSet G v { val := e, property := he }).toProd.fst = v
    rfl
    -- 🎉 no goals
#align simple_graph.dart_fst_fiber SimpleGraph.dart_fst_fiber

theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v).card = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)
#align simple_graph.dart_fst_fiber_card_eq_degree SimpleGraph.dart_fst_fiber_card_eq_degree

theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  haveI := Classical.decEq V
  -- ⊢ Fintype.card (Dart G) = ∑ v : V, degree G v
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  -- ⊢ card univ = ∑ x : V, card (filter (fun d => d.fst = x) univ)
  exact card_eq_sum_card_fiberwise (by simp)
  -- 🎉 no goals
#align simple_graph.dart_card_eq_sum_degrees SimpleGraph.dart_card_eq_sum_degrees

variable {G} [DecidableEq V]

theorem Dart.edge_fiber (d : G.Dart) :
    (univ.filter fun d' : G.Dart => d'.edge = d.edge) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d
                          -- 🎉 no goals
#align simple_graph.dart.edge_fiber SimpleGraph.Dart.edge_fiber

variable (G)

theorem dart_edge_fiber_card (e : Sym2 V) (h : e ∈ G.edgeSet) :
    (univ.filter fun d : G.Dart => d.edge = e).card = 2 := by
  refine' Sym2.ind (fun v w h => _) e h
  -- ⊢ card (filter (fun d => Dart.edge d = Quotient.mk (Sym2.Rel.setoid V) (v, w)) …
  let d : G.Dart := ⟨(v, w), h⟩
  -- ⊢ card (filter (fun d => Dart.edge d = Quotient.mk (Sym2.Rel.setoid V) (v, w)) …
  convert congr_arg card d.edge_fiber
  -- ⊢ 2 = card {d, Dart.symm d}
  rw [card_insert_of_not_mem, card_singleton]
  -- ⊢ ¬d ∈ {Dart.symm d}
  rw [mem_singleton]
  -- ⊢ ¬d = Dart.symm d
  exact d.symm_ne.symm
  -- 🎉 no goals
#align simple_graph.dart_edge_fiber_card SimpleGraph.dart_edge_fiber_card

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
  rw [← card_univ]
  -- ⊢ card univ = 2 * card (edgeFinset G)
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  -- ⊢ ∀ (x : Sym2 V), x ∈ edgeFinset G → card (filter (fun x_1 => Dart.edge x_1 =  …
  intro e h
  -- ⊢ card (filter (fun x => Dart.edge x = e) univ) = 2
  apply G.dart_edge_fiber_card e
  -- ⊢ e ∈ edgeSet G
  rwa [← mem_edgeFinset]
  -- 🎉 no goals
#align simple_graph.dart_card_eq_twice_card_edges SimpleGraph.dart_card_eq_twice_card_edges

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `SimpleGraph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges
#align simple_graph.sum_degrees_eq_twice_card_edges SimpleGraph.sum_degrees_eq_twice_card_edges

end DegreeSum

/-- The handshaking lemma.  See also `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even (univ.filter fun v => Odd (G.degree v)).card := by
  classical
    have h := congr_arg (fun n => ↑n : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
    simp only [ZMod.nat_cast_self, zero_mul, Nat.cast_mul] at h
    rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
    rw [@sum_congr _ _ _ _ (fun v => (G.degree v : ZMod 2)) (fun _v => (1 : ZMod 2)) _ rfl] at h
    · simp only [filter_congr, mul_one, nsmul_eq_mul, sum_const, Ne.def] at h
      rw [← ZMod.eq_zero_iff_even]
      convert h
      exact ZMod.ne_zero_iff_odd.symm
    · intro v
      simp only [true_and_iff, mem_filter, mem_univ, Ne.def]
      rw [ZMod.eq_zero_iff_even, ZMod.eq_one_iff_odd, Nat.odd_iff_not_even, imp_self]
      trivial
#align simple_graph.even_card_odd_degree_vertices SimpleGraph.even_card_odd_degree_vertices

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd (univ.filter fun w => w ≠ v ∧ Odd (G.degree w)).card := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  -- ⊢ Odd (card (filter (fun w => w ≠ v ∧ Odd (degree G w)) univ))
  have hk : 0 < k := by
    have hh : (filter (fun v : V => Odd (G.degree v)) univ).Nonempty := by
      use v
      simp only [true_and_iff, mem_filter, mem_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, zero_lt_mul_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [hc, filter_congr]
  -- ⊢ Odd (card (filter (fun w => Odd (degree G w) ∧ w ≠ v) univ))
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  -- ⊢ Odd (card (filter (fun w => Odd (degree G w)) univ) - 1)
  · refine' ⟨k - 1, tsub_eq_of_eq_add <| hg.trans _⟩
    -- ⊢ k + k = 2 * (k - 1) + 1 + 1
    rw [add_assoc, one_add_one_eq_two, ← Nat.mul_succ, ← two_mul]
    -- ⊢ 2 * k = 2 * Nat.succ (k - 1)
    congr
    -- ⊢ k = Nat.succ (k - 1)
    exact (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 hk).symm
    -- 🎉 no goals
  · simpa only [true_and_iff, mem_filter, mem_univ]
    -- 🎉 no goals
#align simple_graph.odd_card_odd_degree_vertices_ne SimpleGraph.odd_card_odd_degree_vertices_ne

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  haveI := Classical.decEq V
  -- ⊢ ∃ w, w ≠ v ∧ Odd (degree G w)
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  -- ⊢ ∃ w, w ≠ v ∧ Odd (degree G w)
  have hg' : (filter (fun w : V => w ≠ v ∧ Odd (G.degree w)) univ).card > 0 := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  -- ⊢ ∃ w, w ≠ v ∧ Odd (degree G w)
  simp only [true_and_iff, mem_filter, mem_univ, Ne.def] at hw
  -- ⊢ ∃ w, w ≠ v ∧ Odd (degree G w)
  exact ⟨w, hw⟩
  -- 🎉 no goals
#align simple_graph.exists_ne_odd_degree_of_exists_odd_degree SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree

end SimpleGraph
