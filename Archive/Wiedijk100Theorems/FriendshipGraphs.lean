/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller

! This file was ported from Lean 3 source module wiedijk_100_theorems.friendship_graphs
! leanprover-community/mathlib commit 5563b1b49e86e135e8c7b556da5ad2f5ff881cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The Friendship Theorem

## Definitions and Statement
- A `friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices, although some steps could equivalently
be phrased in terms of counting walks.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

## References
- [P. Erdős, A. Rényi, V. Sós, *On A Problem of Graph Theory*][erdosrenyisos]
- [C. Huneke, *The Friendship Theorem*][huneke2002]

-/


open scoped Classical BigOperators

namespace Theorems100

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

/-- This property of a graph is the hypothesis of the friendship theorem:
every pair of nonadjacent vertices has exactly one common friend,
a vertex to which both are adjacent.
-/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1
#align theorems_100.friendship Theorems100.Friendship

/-- A politician is a vertex that is adjacent to all other vertices.
-/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w
#align theorems_100.exists_politician Theorems100.ExistsPolitician

end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)

/-- One characterization of a friendship graph is that there is exactly one walk of length 2
  between distinct vertices. These walks are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) : (G.adjMatrix R ^ 2) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp [common_neighbors, neighbor_finset_eq_filter, Finset.filter_filter, and_comm', ←
    neighbor_finset_def]
#align theorems_100.friendship.adj_matrix_sq_of_ne Theorems100.Friendship.adjMatrix_sq_of_ne

/-- This calculation amounts to counting the number of length 3 walks between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
theorem adjMatrix_pow_three_of_not_adj {v w : V} (non_adj : ¬G.Adj v w) :
    (G.adjMatrix R ^ 3) v w = degree G v := by
  rw [pow_succ, mul_eq_mul, adj_matrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  rw [adj_matrix_sq_of_ne _ hG, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighbor_finset] at hx 
  exact non_adj hx
#align theorems_100.friendship.adj_matrix_pow_three_of_not_adj Theorems100.Friendship.adjMatrix_pow_three_of_not_adj

variable {R}

/-- As `v` and `w` not being adjacent implies
  `degree G v = ((G.adj_matrix R) ^ 3) v w` and `degree G w = ((G.adj_matrix R) ^ 3) v w`,
  the degrees are equal if `((G.adj_matrix R) ^ 3) v w = ((G.adj_matrix R) ^ 3) w v`

  This is true as the adjacency matrix is symmetric. -/
theorem degree_eq_of_not_adj {v w : V} (hvw : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w), ←
    adj_matrix_pow_three_of_not_adj ℕ hG hvw, ←
    adj_matrix_pow_three_of_not_adj ℕ hG fun h => hvw (G.symm h)]
  conv_lhs => rw [← transpose_adj_matrix]
  simp only [pow_succ, sq, mul_eq_mul, ← transpose_mul, transpose_apply]
  simp only [← mul_eq_mul, mul_assoc]
#align theorems_100.friendship.degree_eq_of_not_adj Theorems100.Friendship.degree_eq_of_not_adj

/-- Let `A` be the adjacency matrix of a graph `G`.
  If `G` is a friendship graph, then all of the off-diagonal entries of `A^2` are 1.
  If `G` is `d`-regular, then all of the diagonal entries of `A^2` are `d`.
  Putting these together determines `A^2` exactly for a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = fun v w => if v = w then d else 1 := by
  ext (v w); by_cases h : v = w
  · rw [h, sq, mul_eq_mul, adj_matrix_mul_self_apply_self, hd]; simp
  · rw [adj_matrix_sq_of_ne R hG h, if_neg h]
#align theorems_100.friendship.adj_matrix_sq_of_regular Theorems100.Friendship.adjMatrix_sq_of_regular

theorem adjMatrix_sq_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = fun _ _ => 1 := by
  simp [adj_matrix_sq_of_regular hG hd, dmod]
#align theorems_100.friendship.adj_matrix_sq_mod_p_of_regular Theorems100.Friendship.adjMatrix_sq_mod_p_of_regular

section Nonempty

variable [Nonempty V]

/-- If `G` is a friendship graph without a politician (a vertex adjacent to all others), then
  it is regular. We have shown that nonadjacent vertices of a friendship graph have the same degree,
  and if there isn't a politician, we can show this for adjacent vertices by finding a vertex
  neither is adjacent to, and then using transitivity. -/
theorem is_regular_of_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Theorems100.ExistsPolitician] at hG' 
  push_neg at hG' 
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.common_neighbors v w → x = a := by
    intro x hx
    have h' := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h' 
    injection h'
  apply hxy'
  rw [key ((mem_common_neighbors G).mpr ⟨hvx, G.symm hxw⟩),
    key ((mem_common_neighbors G).mpr ⟨hvy, G.symm hcontra⟩)]
#align theorems_100.friendship.is_regular_of_not_exists_politician Theorems100.Friendship.is_regular_of_not_existsPolitician

/-- Let `A` be the adjacency matrix of a `d`-regular friendship graph, and let `v` be a vector
  all of whose components are `1`. Then `v` is an eigenvector of `A ^ 2`, and we can compute
  the eigenvalue to be `d * d`, or as `d + (fintype.card V - 1)`, so those quantities must be equal.

  This essentially means that the graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans (G.adj_matrix ℕ ^ 2).mulVec (fun _ => 1) v
  · rw [adj_matrix_sq_of_regular hG hd, mul_vec, dot_product, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, eq_self_iff_true, mem_erase, not_true,
      Ne.def, not_false_iff, add_right_inj, false_and_iff]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]; · rfl
    intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, mul_eq_mul, ← mul_vec_mul_vec]
    simp [adj_matrix_mul_vec_const_apply_of_regular hd, neighbor_finset,
      card_neighbor_set_eq_degree, hd v]
#align theorems_100.friendship.card_of_regular Theorems100.Friendship.card_of_regular

/-- The size of a `d`-regular friendship graph is `1 mod (d-1)`, and thus `1 mod p` for a
  factor `p ∣ d-1`. -/
theorem card_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) :
    (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_left_eq_self, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n => (↑n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]
#align theorems_100.friendship.card_mod_p_of_regular Theorems100.Friendship.card_mod_p_of_regular

end Nonempty

theorem adjMatrix_sq_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) :
    (G.adjMatrix R * fun _ _ => 1) = fun _ _ => d := by ext x; simp [← hd x, degree]
#align theorems_100.friendship.adj_matrix_sq_mul_const_one_of_regular Theorems100.Friendship.adjMatrix_sq_mul_const_one_of_regular

theorem adjMatrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : (G.adjMatrix (ZMod p) * fun _ _ => 1) = fun _ _ => 1 := by
  rw [adj_matrix_sq_mul_const_one_of_regular hd, dmod]
#align theorems_100.friendship.adj_matrix_mul_const_one_mod_p_of_regular Theorems100.Friendship.adjMatrix_mul_const_one_mod_p_of_regular

/-- Modulo a factor of `d-1`, the square and all higher powers of the adjacency matrix
  of a `d`-regular friendship graph reduce to the matrix whose entries are all 1. -/
theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) : G.adjMatrix (ZMod p) ^ k = fun _ _ => 1 :=
  by
  iterate 2 cases' k with k; · exfalso; linarith
  induction' k with k hind
  · exact adj_matrix_sq_mod_p_of_regular hG dmod hd
  rw [pow_succ, hind (Nat.le_add_left 2 k)]
  exact adj_matrix_mul_const_one_mod_p_of_regular dmod hd
#align theorems_100.friendship.adj_matrix_pow_mod_p_of_regular Theorems100.Friendship.adjMatrix_pow_mod_p_of_regular

variable [Nonempty V]

/-- This is the main proof. Assuming that `3 ≤ d`, we take `p` to be a prime factor of `d-1`.
  Then the `p`th power of the adjacency matrix of a `d`-regular friendship graph must have trace 1
  mod `p`, but we can also show that the trace must be the `p`th power of the trace of the original
  adjacency matrix, which is 0, a contradiction.
-/
theorem false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).minFac
  have p_dvd_d_pred := (ZMod.nat_cast_zmod_eq_zero_iff_dvd _ _).mpr (d - 1).minFac_dvd
  have dpos : 0 < d := by linarith
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast
  haveI : Fact p.prime := ⟨Nat.minFac_prime (by linarith)⟩
  have hp2 : 2 ≤ p := (Fact.out p.prime).two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [← Nat.succ_pred_eq_of_pos dpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    simp only [add_left_eq_self, Nat.cast_add, Nat.cast_one]
    exact p_dvd_d_pred
  have Vmod := card_mod_p_of_regular hG dmod hd
  -- now we reduce to a trace calculation
  have := ZMod.trace_pow_card (G.adj_matrix (ZMod p))
  contrapose! this; clear this
  -- the trace is 0 mod p when computed one way
  rw [trace_adj_matrix, zero_pow (Fact.out p.prime).Pos]
  -- but the trace is 1 mod p when computed the other way
  rw [adj_matrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod 
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, LinearMap.coe_mk, sum_const]
  rw [Vmod, ← Nat.cast_one, ZMod.nat_cast_zmod_eq_zero_iff_dvd, Nat.dvd_one, Nat.minFac_eq_one_iff]
  linarith
#align theorems_100.friendship.false_of_three_le_degree Theorems100.Friendship.false_of_three_le_degree

/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex, which is
  trivially a politician. -/
theorem existsPolitician_of_degree_le_one (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) :
    ExistsPolitician G := by
  have sq : d * d = d := by interval_cases <;> norm_num
  have h := card_of_regular hG hd
  rw [sq] at h 
  have : Fintype.card V ≤ 1 := by
    cases' Fintype.card V with n
    · exact zero_le _
    · have : n = 0 := by
        rw [Nat.succ_sub_succ_eq_sub, tsub_zero] at h 
        linarith
      subst n
  use Classical.arbitrary V
  intro w h; exfalso
  apply h
  apply fintype.card_le_one_iff.mp this
#align theorems_100.friendship.exists_politician_of_degree_le_one Theorems100.Friendship.existsPolitician_of_degree_le_one

/-- If `d = 2`, a `d`-regular friendship graph has 3 vertices, so it must be complete graph,
  and all the vertices are politicians. -/
theorem neighborFinset_eq_of_degree_eq_two (hd : G.IsRegularOfDegree 2) (v : V) :
    G.neighborFinset v = Finset.univ.eraseₓ v := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.subset_iff]
    intro x
    rw [mem_neighbor_finset, Finset.mem_erase]
    exact fun h => ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
  convert_to 2 ≤ _
  · convert_to _ = Fintype.card V - 1
    · have hfr := card_of_regular hG hd
      linarith
    · exact Finset.card_erase_of_mem (Finset.mem_univ _)
  · dsimp [is_regular_of_degree, degree] at hd 
    rw [hd]
#align theorems_100.friendship.neighbor_finset_eq_of_degree_eq_two Theorems100.Friendship.neighborFinset_eq_of_degree_eq_two

theorem existsPolitician_of_degree_eq_two (hd : G.IsRegularOfDegree 2) : ExistsPolitician G := by
  have v := Classical.arbitrary V
  use v
  intro w hvw
  rw [← mem_neighbor_finset, neighbor_finset_eq_of_degree_eq_two hG hd v, Finset.mem_erase]
  exact ⟨hvw.symm, Finset.mem_univ _⟩
#align theorems_100.friendship.exists_politician_of_degree_eq_two Theorems100.Friendship.existsPolitician_of_degree_eq_two

theorem existsPolitician_of_degree_le_two (hd : G.IsRegularOfDegree d) (h : d ≤ 2) :
    ExistsPolitician G := by
  interval_cases
  iterate 2 apply exists_politician_of_degree_le_one hG hd; norm_num
  · exact exists_politician_of_degree_eq_two hG hd
#align theorems_100.friendship.exists_politician_of_degree_le_two Theorems100.Friendship.existsPolitician_of_degree_le_two

end Friendship

/-- **Friendship theorem**: We wish to show that a friendship graph has a politician (a vertex
  adjacent to all others). We proceed by contradiction, and assume the graph has no politician.
  We have already proven that a friendship graph with no politician is `d`-regular for some `d`,
  and now we do casework on `d`.
  If the degree is at most 2, we observe by casework that it has a politician anyway.
  If the degree is at least 3, the graph cannot exist. -/
theorem friendship_theorem [Nonempty V] : ExistsPolitician G := by
  by_contra npG
  rcases hG.is_regular_of_not_exists_politician npG with ⟨d, dreg⟩
  cases' lt_or_le d 3 with dle2 dge3
  · exact npG (hG.exists_politician_of_degree_le_two dreg (nat.lt_succ_iff.mp dle2))
  · exact hG.false_of_three_le_degree dreg dge3
#align theorems_100.friendship_theorem Theorems100.friendship_theorem

end Theorems100

