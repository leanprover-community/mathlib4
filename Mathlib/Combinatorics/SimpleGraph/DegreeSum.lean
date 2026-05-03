/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Youheng Luo
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

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
- `SimpleGraph.sum_degrees_option_zmod_two` is the handshaking lemma for `Option I` over `ZMod 2`.
- `SimpleGraph.degree_none_zmod_two_eq_sum` is the `simp`-normal form of the above.
- `SimpleGraph.card_degree_one_option_eq_outer_zmod_two` relates the count of degree-1 inner
  vertices to the outer vertex degree modulo 2.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/

public section

assert_not_exists Field TwoSidedIdeal

open Finset

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
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

variable {G} in
theorem Dart.edge_fiber [DecidableEq V] (d : G.Dart) :
    ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d

theorem dart_edge_fiber_card [DecidableEq V] (e : Sym2 V) (h : e ∈ G.edgeSet) :
    #{d : G.Dart | d.edge = e} = 2 := by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert congr_arg card d.edge_fiber
  rw [card_insert_of_notMem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * #G.edgeFinset := by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe, mem_edgeFinset]; apply Dart.edge_mem]
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
  refine card_bij' (fun d _ ↦ (d.fst, d.snd)) (fun xy h ↦ ⟨xy, (mem_filter.1 h).2⟩)
    ?_ ?_ ?_ ?_
    <;> simp

/-- The degree-sum formula only counting over the vertices that form edges.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version. -/
theorem sum_degrees_support_eq_twice_card_edges :
    ∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset := by
  classical
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, left_eq_add]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_notMem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

end DegreeSum

/-- The handshaking lemma.  See also `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even #{v | Odd (G.degree v)} := by
  classical
    have h := congr_arg (fun n => ↑n : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
    simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
    rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
    rw [sum_congr (g := fun _v ↦ (1 : ZMod 2)) rfl] at h
    · simp only [mul_one, nsmul_eq_mul, sum_const, Ne] at h
      rw [← ZMod.natCast_eq_zero_iff_even]
      convert h
      exact ZMod.natCast_ne_zero_iff_odd.symm
    · intro v
      rw [mem_filter_univ, Ne, ZMod.natCast_eq_zero_iff_even, ZMod.natCast_eq_one_iff_odd,
        ← Nat.not_even_iff_odd]
      tauto

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd #{w | w ≠ v ∧ Odd (G.degree w)} := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      rw [mem_filter_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) =
      fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [hc]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine ⟨k - 1, tsub_eq_of_eq_add <| hg.trans ?_⟩
    lia
  · rwa [mem_filter_univ]

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  haveI := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w ≠ v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  rw [mem_filter_univ] at hw
  exact ⟨w, hw⟩

/-- For a graph on `Option I`, the degree of the outer vertex `none` plus the
sum of degrees of all inner vertices `some i` is 0 modulo 2.

This is the handshaking lemma applied to `Option I`. -/
theorem sum_degrees_option_zmod_two {I : Type*} [Fintype I]
    (G : SimpleGraph (Option I)) [DecidableRel G.Adj] :
    (G.degree none : ZMod 2) + ∑ i : I, (G.degree (some i) : ZMod 2) = 0 := by
  have h : (∑ v : Option I, (G.degree v : ZMod 2)) = 0 := by
    have := congr_arg (Nat.cast : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
    simp only [Nat.cast_mul, CharP.cast_eq_zero, zero_mul] at this
    rw [← this, Nat.cast_sum]
  rw [Fintype.sum_option] at h
  exact h

/-- The degree of the outer vertex `none` equals the sum of degrees of all inner vertices
modulo 2. -/
@[simp]
theorem degree_none_zmod_two_eq_sum {I : Type*} [Fintype I]
    (G : SimpleGraph (Option I)) [DecidableRel G.Adj] :
    (G.degree none : ZMod 2) = ∑ i : I, (G.degree (some i) : ZMod 2) := by
  have h := sum_degrees_option_zmod_two G
  exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h

/-- In a graph with an outer vertex `none` and inner vertices `some i`,
if every inner vertex has degree at most 2, then the number of inner vertices with
degree exactly 1 is congruent to the degree of the outer vertex modulo 2.

The bound `≤ 2` ensures that `(G.degree (some i) : ZMod 2) = 1` is equivalent
to `G.degree (some i) = 1` (since `(0 : ZMod 2) = 0` and `(2 : ZMod 2) = 0`).
While a more general formulation could require `Odd (G.degree (some i))` instead,
the `≤ 2` bound is chosen as it naturally fits geometric applications like dual graphs
of triangulations where edges are shared by at most 2 faces. -/
@[simp]
theorem card_degree_one_option_eq_outer_zmod_two {I : Type*} [Fintype I]
    (G : SimpleGraph (Option I)) [DecidableRel G.Adj]
    (h_le : ∀ i : I, G.degree (some i) ≤ 2) :
    (#{i : I | G.degree (some i) = 1} : ZMod 2) = (G.degree none : ZMod 2) := by
  simp only [degree_none_zmod_two_eq_sum]
  symm
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro x _
  have hz : (G.degree (some x) : ZMod 2) = 1 ↔ G.degree (some x) = 1 := by
    have hx := h_le x
    have : G.degree (some x) = 0 ∨ G.degree (some x) = 1 ∨ G.degree (some x) = 2 := by omega
    rcases this with h | h | h <;> simp only [h] <;> decide
  split_ifs with heq
  · exact hz.mpr heq
  · have h_not : (G.degree (some x) : ZMod 2) ≠ 1 := (not_congr hz).mpr heq
    revert h_not
    generalize (G.degree (some x) : ZMod 2) = z
    intro h
    fin_cases z
    · rfl
    · exact absurd rfl h

end SimpleGraph
