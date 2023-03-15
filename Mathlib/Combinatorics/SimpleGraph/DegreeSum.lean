/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.degree_sum
! leanprover-community/mathlib commit 90659cbe25e59ec302e2fb92b00e9732160cc620
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Zmod.Parity

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.even_card_odd_degree_vertices` is the handshaking lemma.
- `simple_graph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
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

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    (univ.filterₓ fun d : G.Dart => d.fst = v) = univ.image (G.dartOfNeighborSet v) :=
  by
  ext d
  simp only [mem_image, true_and_iff, mem_filter, SetCoe.exists, mem_univ, exists_prop_of_true]
  constructor
  · rintro rfl
    exact ⟨_, d.is_adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl
#align simple_graph.dart_fst_fiber SimpleGraph.dart_fst_fiber

theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    (univ.filterₓ fun d : G.Dart => d.fst = v).card = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighbor_set_eq_degree] using
    card_image_of_injective univ (G.dart_of_neighbor_set_injective v)
#align simple_graph.dart_fst_fiber_card_eq_degree SimpleGraph.dart_fst_fiber_card_eq_degree

theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v :=
  by
  haveI := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)
#align simple_graph.dart_card_eq_sum_degrees SimpleGraph.dart_card_eq_sum_degrees

variable {G} [DecidableEq V]

theorem Dart.edge_fiber (d : G.Dart) :
    (univ.filterₓ fun d' : G.Dart => d'.edge = d.edge) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d
#align simple_graph.dart.edge_fiber SimpleGraph.Dart.edge_fiber

variable (G)

theorem dart_edge_fiber_card (e : Sym2 V) (h : e ∈ G.edgeSetEmbedding) :
    (univ.filterₓ fun d : G.Dart => d.edge = e).card = 2 :=
  by
  refine' Sym2.ind (fun v w h => _) e h
  let d : G.dart := ⟨(v, w), h⟩
  convert congr_arg card d.edge_fiber
  rw [card_insert_of_not_mem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm
#align simple_graph.dart_edge_fiber_card SimpleGraph.dart_edge_fiber_card

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * G.edgeFinset.card :=
  by
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset fun d h =>
      by
      rw [mem_edge_finset]
      apply dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edge_finset]
#align simple_graph.dart_card_eq_twice_card_edges SimpleGraph.dart_card_eq_twice_card_edges

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : (∑ v, G.degree v) = 2 * G.edgeFinset.card :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges
#align simple_graph.sum_degrees_eq_twice_card_edges SimpleGraph.sum_degrees_eq_twice_card_edges

end DegreeSum

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even (univ.filterₓ fun v => Odd (G.degree v)).card := by
  classical
    have h := congr_arg (fun n => ↑n : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
    simp only [ZMod.nat_cast_self, MulZeroClass.zero_mul, Nat.cast_mul] at h
    rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
    rw [@sum_congr _ _ _ _ (fun v => (G.degree v : ZMod 2)) (fun v => (1 : ZMod 2)) _ rfl] at h
    · simp only [filter_congr_decidable, mul_one, nsmul_eq_mul, sum_const, Ne.def] at h
      rw [← ZMod.eq_zero_iff_even]
      convert h
      ext v
      rw [← ZMod.ne_zero_iff_odd]
    · intro v
      simp only [true_and_iff, mem_filter, mem_univ, Ne.def]
      rw [ZMod.eq_zero_iff_even, ZMod.eq_one_iff_odd, Nat.odd_iff_not_even, imp_self]
      trivial
#align simple_graph.even_card_odd_degree_vertices SimpleGraph.even_card_odd_degree_vertices

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd (univ.filterₓ fun w => w ≠ v ∧ Odd (G.degree w)).card :=
  by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k :=
    by
    have hh : (Filter (fun v : V => Odd (G.degree v)) univ).Nonempty :=
      by
      use v
      simp only [true_and_iff, mem_filter, mem_univ]
      use h
    rwa [← card_pos, hg, ← two_mul, zero_lt_mul_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v :=
    by
    ext w
    rw [and_comm']
  simp only [hc, filter_congr_decidable]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine' ⟨k - 1, tsub_eq_of_eq_add <| hg.trans _⟩
    rw [add_assoc, one_add_one_eq_two, ← Nat.mul_succ, ← two_mul]
    congr
    exact (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 hk).symm
  · simpa only [true_and_iff, mem_filter, mem_univ]
#align simple_graph.odd_card_odd_degree_vertices_ne SimpleGraph.odd_card_odd_degree_vertices_ne

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : ∃ w : V, w ≠ v ∧ Odd (G.degree w) :=
  by
  haveI := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : (Filter (fun w : V => w ≠ v ∧ Odd (G.degree w)) univ).card > 0 :=
    by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  simp only [true_and_iff, mem_filter, mem_univ, Ne.def] at hw
  exact ⟨w, hw⟩
#align simple_graph.exists_ne_odd_degree_of_exists_odd_degree SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree

end SimpleGraph

