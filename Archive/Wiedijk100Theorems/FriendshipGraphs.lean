/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField

/-!
# The friendship theorem

Every finite friendship graph, where every distinct pair of vertices has exactly one
common neighbor, has a universal vertex adjacent to every other vertex. [erdosrenyisos]
The proof [huneke2002] revolves around the theory of adjacency matrices,
although some steps could equivalently be phrased in terms of counting walks.

Let `G` be a finite friendship graph. We first show that any two nonadjacent vertices have
the same degree, so if there is no universal vertex it is `d`-regular for some `d : ℕ`
and has `d ^ 2 - d + 1` vertices.

The case `d ≤ 2` is handled separately. If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
If `A` is `G`'s adjacency matrix over `ZMod p`, we show that `tr(A ^ p) = 1`,
contradicting the fact that `tr(A ^ p) = tr(A) ^ p = 0`.
-/

public section

namespace Theorems100

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V]

open scoped Classical in
/-- A friendship graph has exactly one common neighbor for every distinct pair of vertices. -/
def IsFriendship (G : SimpleGraph V) : Prop :=
  ∀ ⦃v w⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

variable {G : SimpleGraph V} {R : Type*} [Semiring R] {d : ℕ} (hG : IsFriendship G)

include hG

namespace IsFriendship

open scoped Classical in
lemma adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) : (G.adjMatrix R ^ 2) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw, mul_adjMatrix_apply, neighborFinset_eq_filter]
  simp_rw [adjMatrix_apply, sum_boole, filter_filter, and_comm, Fintype.card_ofFinset]
  congr

open scoped Classical in
lemma adjMatrix_pow_three_of_not_adj {v w : V} (na : ¬G.Adj v w) :
    (G.adjMatrix ℕ ^ 3) v w = degree G v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones]
  congr! with x
  exact hG.adjMatrix_sq_of_ne (by rintro ⟨rfl⟩; simp_all)

open scoped Classical in
lemma degree_eq_of_not_adj {v w : V} (na : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← hG.adjMatrix_pow_three_of_not_adj na,
    ← hG.adjMatrix_pow_three_of_not_adj fun h ↦ na h.symm, (G.isSymm_adjMatrix.pow 3).apply]

open scoped Classical in
lemma adjMatrix_sq_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = of fun v w ↦ if v = w then (d : R) else 1 := by
  ext v w; by_cases h : v = w
  · rw [h, sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [hG.adjMatrix_sq_of_ne h, of_apply, ite_eq_right h]

open scoped Classical in
lemma adjMatrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of fun _ _ ↦ 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp [hG.adjMatrix_sq_of_regular hd, dmod]
  | succ k hk ih => rw [pow_succ', ih]; ext x; simp [hd x, dmod]

variable [Nonempty V]

open scoped Classical in
lemma isRegular_of_not_exists_isUniversal (nu : ¬∃ v, G.IsUniversal v) :
    ∃ d, G.IsRegularOfDegree d := by
  let v := Classical.arbitrary V
  refine ⟨G.degree v, fun w ↦ ?_⟩
  by_cases! a₀ : ¬G.Adj v w; · rw [hG.degree_eq_of_not_adj a₀]
  simp_rw [IsUniversal, not_exists, not_forall] at nu
  obtain ⟨x, n₁, a₁⟩ := nu v
  obtain ⟨y, n₂, a₂⟩ := nu w
  by_cases! a₃ : ¬G.Adj v y; · rw [hG.degree_eq_of_not_adj a₂, hG.degree_eq_of_not_adj a₃]
  by_cases! a₄ : ¬G.Adj x w; · rw [hG.degree_eq_of_not_adj a₁, hG.degree_eq_of_not_adj a₄]
  obtain ⟨⟨z, mz⟩, key⟩ := Fintype.card_eq_one_iff.mp (hG n₁)
  simp_rw [Subtype.forall, mem_commonNeighbors, Subtype.mk.injEq, and_imp] at key
  rw [hG.degree_eq_of_not_adj a₁, hG.degree_eq_of_not_adj a₂]
  exact hG.degree_eq_of_not_adj fun a₅ ↦ by grind [key _ a₀ a₄, key _ a₃ a₅.symm]

open scoped Classical in
/-- The all-ones vector is an eigenvector of `A ^ 2`. We can compute the eigenvalue to be
`d ^ 2 = d + (Fintype.card V - 1)`, so the graph has `d ^ 2 - d + 1` vertices. -/
lemma card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  let v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ fun _ ↦ 1) v
  · rw [hG.adjMatrix_sq_of_regular hd, mulVec, dotProduct, ← insert_erase (mem_univ v),
      sum_insert (by simp), of_apply, ite_eq_left rfl, Nat.cast_id, mul_one, add_right_inj]
    simp_rw [mul_one, of_apply]
    rw [sum_const_nat (m := 1) (by grind), card_erase_of_mem (by simp), mul_one, card_univ]
  · rw [sq, ← mulVec_mulVec, Function.const_def, adjMatrix_mulVec_apply]
    simp_rw [adjMatrix_mulVec_const_apply_of_regular hd]
    simp [hd v]

open scoped Classical in
theorem degree_le_two (hd : G.IsRegularOfDegree d) : d ≤ 2 := by
  by_contra! con
  let p := (d - 1).minFac
  have pp : Fact p.Prime := ⟨Nat.minFac_prime (by lia)⟩
  have gp := pp.out.two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [show d = d - 1 + 1 by lia, Nat.cast_add_one, add_eq_right, ZMod.natCast_eq_zero_iff]
    exact (d - 1).minFac_dvd
  have Vmod : (#(univ : Finset V) : ZMod p) = 1 := by
    rw [← (#univ).sub_one_add_one (by simp), Nat.cast_add_one, add_eq_right]
    simpa [dmod] using congr(($(hG.card_of_regular hd) : ZMod p))
  have key := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  simp_rw [trace_adjMatrix, zero_pow pp.out.ne_zero, hG.adjMatrix_pow_mod_p_of_regular dmod hd gp,
    trace, Matrix.diag, of_apply, sum_const, nsmul_eq_mul, Vmod, one_mul, one_ne_zero] at key

open scoped Classical in
theorem exists_isUniversal_of_regular (hd : G.IsRegularOfDegree d) :
    ∃ v, G.IsUniversal v := by
  have v := Classical.arbitrary V
  have ld := hG.degree_le_two hd
  have ce := hG.card_of_regular hd
  interval_cases d
  all_goals refine ⟨v, fun w nw ↦ ?_⟩
  iterate 2 exact nw.elim (Fintype.card_le_one_iff.mp (by lia) ..)
  suffices G.neighborFinset v = univ.erase v by simp [← mem_neighborFinset, this, nw.symm]
  apply eq_of_subset_of_card_le <;> grind [mem_neighborFinset, card_neighborFinset_eq_degree, hd v]

end IsFriendship

theorem friendship_theorem [Nonempty V] : ∃ v, G.IsUniversal v := by
  by_contra con
  obtain ⟨d, hd⟩ := hG.isRegular_of_not_exists_isUniversal con
  exact con.elim (hG.exists_isUniversal_of_regular hd)

end Theorems100
