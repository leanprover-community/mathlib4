/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic

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

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ, exists_prop_of_true]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl

theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    #{d : G.Dart | d.fst = v} = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)

theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  haveI := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)

variable {G}

theorem Dart.edge_fiber [DecidableEq V] (d : G.Dart) :
    ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d

variable (G)

theorem dart_edge_fiber_card [DecidableEq V] (e : Sym2 V) (h : e ∈ G.edgeSet) :
    #{d : G.Dart | d.edge = e} = 2 := by
  induction' e with v w
  let d : G.Dart := ⟨(v, w), h⟩
  convert congr_arg card d.edge_fiber
  rw [card_insert_of_not_mem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * #G.edgeFinset := by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edgeFinset]

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `SimpleGraph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

lemma two_mul_card_edgeFinset : 2 * #G.edgeFinset = #(univ.filter fun (x, y) ↦ G.Adj x y) := by
  rw [← dart_card_eq_twice_card_edges, ← card_univ]
  refine card_bij' (fun d _ ↦ (d.fst, d.snd)) (fun xy h ↦ ⟨xy, (mem_filter.1 h).2⟩) ?_ ?_ ?_ ?_
    <;> simp

end DegreeSum

/-- The handshaking lemma.  See also `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even #{v | Odd (G.degree v)} := by
  classical
    have h := congr_arg (fun n => ↑n : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
    simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
    rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
    rw [@sum_congr _ _ _ _ (fun v => (G.degree v : ZMod 2)) (fun _v => (1 : ZMod 2)) _ rfl] at h
    · simp only [filter_congr, mul_one, nsmul_eq_mul, sum_const, Ne] at h
      rw [← ZMod.eq_zero_iff_even]
      convert h
      exact ZMod.ne_zero_iff_odd.symm
    · intro v
      simp only [true_and, mem_filter, mem_univ, Ne]
      rw [ZMod.eq_zero_iff_even, ZMod.eq_one_iff_odd, ← Nat.not_even_iff_odd, imp_self]
      trivial

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd #{w | w ≠ v ∧ Odd (G.degree w)} := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      simp only [true_and, mem_filter, mem_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [hc, filter_congr]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine ⟨k - 1, tsub_eq_of_eq_add <| hg.trans ?_⟩
    rw [add_assoc, one_add_one_eq_two, ← Nat.mul_succ, ← two_mul]
    congr
    omega
  · simpa only [true_and, mem_filter, mem_univ]

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  haveI := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w ≠ v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  simp only [true_and, mem_filter, mem_univ, Ne] at hw
  exact ⟨w, hw⟩

end SimpleGraph
