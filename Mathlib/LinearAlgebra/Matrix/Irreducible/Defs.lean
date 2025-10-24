/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring.RingNF

/-!
# Irreducibility and primitivity of nonnegative matrices

This file develops a graph-theoretic interface for studying the properties of nonnegative square
matrices.

We associate a directed graph (quiver) with a matrix `A`, where an edge `i ⟶ j` exists if and only
if the entry `A i j` is strictly positive. This allows translating algebraic
properties of the matrix (like powers) into graph-theoretic properties of its quiver (like the
existence of paths).

## Main definitions

*   `Matrix.toQuiver A`: The quiver associated with a matrix `A`, where an edge `i ⟶ j` exists if
    `0 < A i j`.
*   `Matrix.IsIrreducible A`: A matrix `A` is defined as irreducible if it is entrywise nonnegative
    and its associated quiver `toQuiver A` is strongly connected. The theorem
    `irreducible_iff_exists_pow_pos` proves this graph-theoretic definition is equivalent to the
    algebraic one in seneta2006 (Def 1.6, p.18): for every pair of indices `(i, j)`, there exists a
    positive integer `k` such that `(A ^ k) i j > 0`.
*   `Matrix.IsPrimitive A`: A matrix `A` is primitive if it is nonnegative and some power `A ^ k`
    is strictly positive (all entries are `> 0`), (seneta2006, Definition 1.1, p.14).

## Main results

*   `pow_entry_pos_iff_exists_path`: Establishes the link between matrix powers and graph theory:
    `(A ^ k) i j > 0` if and only if there is a path of length `k` from `i` to `j` in `toQuiver A`.
*   `irreducible_iff_exists_pow_pos`: Shows the equivalence between the graph-theoretic definition
    of irreducibility (strong connectivity) and the algebraic one (existence of a positive entry
    in some power).
*   `IsPrimitive.to_IsIrreducible`: Proves that a primitive matrix is also irreducible
      (Seneta, p.14).
*   `IsIrreducible.transpose`: Shows that the irreducibility property is preserved under
    transposition.

## Implementation notes

Throughout we work over a `LinearOrderedRing R`. Some results require stronger assumptions,
like `PosMulStrictMono R` or `Nontrivial R`. Some statements expand matrix powers and thus require
`[DecidableEq n]` to reason about finite sums.

## References

*   [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

matrix, nonnegative, positive, power, quiver, graph, irreducible, primitive, perron-frobenius
-/
namespace Matrix

open Finset Quiver Quiver.Path

variable {n R : Type*} [Fintype n] [Ring R] [LinearOrder R]

/-- The directed graph (quiver) associated with a matrix `A`,
with an edge `i ⟶ j` iff `0 < A i j`. -/
def toQuiver (A : Matrix n n R) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

/-- A matrix `A` is irreducible if it is entrywise nonnegative and
its quiver of positive entries (`toQuiver A`) is strongly connected. -/
def IsIrreducible (A : Matrix n n R) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ @IsSStronglyConnected n (toQuiver A)

/-- A matrix `A` is primitive if it is entrywise nonnegative
and some positive power has all entries strictly positive. -/
def IsPrimitive [DecidableEq n] (A : Matrix n n R) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∃ k > 0, ∀ i j, 0 < (A ^ k) i j

variable {A : Matrix n n R}

/-- If `A` is irreducible and `n` is non-trivial then every row has a positive entry. -/
lemma IsIrreducible.exists_pos [Nontrivial n]
    (h_irr : IsIrreducible A) (i : n) :
    ∃ j, 0 < A i j := by
  letI : Quiver n := toQuiver A
  by_contra h_row
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.2 i j
  have h_le : 1 ≤ p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, _hp_eq, hp₁_len⟩ := p.exists_eq_comp_of_le_length (n := 1) h_le
  have hlen_ne : p₁.length ≠ 0 := by simp [hp₁_len]
  obtain ⟨c, p', e, rfl⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).1 hlen_ne
  have hp'_succ : p'.length + 1 = 1 := by
    simpa [Quiver.Path.length_cons] using hp₁_len
  have hp'0 : p'.length = 0 := by
    exact Nat.succ.inj hp'_succ
  have hi_c : i = c := Quiver.Path.eq_of_length_zero p' hp'0
  subst hi_c
  exact (no_out _).false e

/--
For a matrix `A` with nonnegative entries, the `(i, j)`-entry of the `k`-th power `A ^ k`
is strictly positive if and only if there exists a path of length `k` from `i` to `j` in the
quiver associated to `A` via `toQuiver`. -/
theorem pow_entry_pos_iff_exists_path
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := toQuiver A; 0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  induction k generalizing i j with
  | zero =>
    constructor
    · intro h_pos
      by_cases h_eq : i = j
      · subst h_eq
        letI : Quiver n := toQuiver A
        exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · have : (A ^ 0) i j = 0 := by
          simp [pow_zero, h_eq]
        simp_all only [lt_self_iff_false]
    · rintro ⟨p, hp⟩
      letI : Quiver n := toQuiver A
      have h_eq : i = j := Quiver.Path.eq_of_length_zero p hp
      have : 0 < (1 : R) := zero_lt_one
      simp [pow_zero, h_eq]
  | succ m ih =>
    rw [pow_succ, mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ :
          ∃ l ∈ (Finset.univ : Finset n), 0 < (A ^ m) i l * A l j := by
        simpa [Finset.sum_pos_iff_of_nonneg
                 (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))]
          using h_pos
      have hAm_nonneg : 0 ≤ (A ^ m) i l := pow_apply_nonneg hA m i l
      have hA_nonneg' : 0 ≤ A l j := hA l j
      have h_Am : 0 < (A ^ m) i l := by
        by_contra h
        have h_eq : (A ^ m) i l = 0 := le_antisymm (le_of_not_gt h) hAm_nonneg
        simp [h_eq] at hl_pos
      have h_A : 0 < A l j := by
        by_contra h
        have h_eq : A l j = 0 := le_antisymm (le_of_not_gt h) hA_nonneg'
        simp [h_eq] at hl_pos
      obtain ⟨⟨p, hp_len⟩⟩ := (ih i l).mp h_Am
      exact ⟨letI := toQuiver A; p.cons h_A, by
          subst hp_len
          simp only [Path.length_cons]⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos
        exact
          (Finset.sum_pos_iff_of_nonneg
            (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))).2
            ⟨b, Finset.mem_univ b, h_prod⟩

/-- Irreducibility of a nonnegative matrix `A` is equivalent to entrywise positivity of some
power: between any two indices `i, j` there exists a positive integer `k` such that the
`(i, j)`-entry of `A ^ k` is strictly positive. -/
theorem IsIrreducible.iff_exists_pow_pos
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) :
    IsIrreducible A ↔ ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := by
  constructor
  · intro h_irr i j
    letI : Quiver n := toQuiver A
    obtain ⟨p, hp_len⟩ := h_irr.2 i j
    refine ⟨p.length, hp_len, ?_⟩
    have : Nonempty {q : Path i j // q.length = p.length} := ⟨⟨p, rfl⟩⟩
    have hpos :=
      (pow_entry_pos_iff_exists_path (A := A) hA p.length i j).2 this
    simpa using hpos
  · intro h_exists
    constructor
    · exact hA
    · intro i j
      obtain ⟨k, hk_pos, hk_entry⟩ := h_exists i j
      letI : Quiver n := toQuiver A
      obtain ⟨⟨p, hp_len⟩⟩ :=
        (pow_entry_pos_iff_exists_path (A := A) hA k i j).mp hk_entry
      subst hp_len
      exact ⟨p, hk_pos⟩

/-- If a nonnegative square matrix `A` is primitive, then `A` is irreducible. -/
theorem IsPrimitive.to_IsIrreducible
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (h_prim : IsPrimitive A) : IsIrreducible A := by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  refine ⟨h_nonneg, fun i j ↦ ?_⟩
  letI : Quiver n := toQuiver A
  have ⟨⟨p, hp⟩⟩ : Nonempty {p : Path i j // p.length = k} :=
    (pow_entry_pos_iff_exists_path h_nonneg k i j).mp (hk_all i j)
  exact ⟨p, hp ▸ hk_pos⟩

/-! ## Transposition -/

/-- Reverse a path in `toQuiver A` to a path in `toQuiver Aᵀ`, swapping endpoints. -/
def transposeRev
    {n R : Type*} [Ring R] [LinearOrder R] {A : Matrix n n R} :
    ∀ {i j : n}, (@Quiver.Path n (toQuiver A) i j) →
      (@Quiver.Path n (toQuiver Aᵀ) j i) := by
  letI : Quiver n := toQuiver A
  intro i j p
  induction p with
  | nil =>
    exact (@Quiver.Path.nil _ (toQuiver Aᵀ) _)
  | @cons b c q e ih =>
    have eT : @Quiver.Hom n (toQuiver Aᵀ) c b := by
      change 0 < (Aᵀ) c b
      simpa [Matrix.transpose_apply] using e
    exact (@Quiver.Path.comp n (toQuiver Aᵀ) c b i (@Quiver.Hom.toPath n (toQuiver Aᵀ) c b eT) ih)

variable {n R : Type*} [Ring R] [LinearOrder R]
variable {A : Matrix n n R}

/-- Irreducibility is invariant under transpose. -/
theorem IsIrreducible.transpose
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA : IsIrreducible A) : IsIrreducible Aᵀ := by
  have hA_T_nonneg : ∀ i j, 0 ≤ (Aᵀ) i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA_nonneg j i
  refine ⟨hA_T_nonneg, ?_⟩
  intro i j
  letI : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.2 j i
  cases p with
  | nil =>
      exact False.elim ((lt_irrefl (0 : Nat)) (by simp [Quiver.Path.length] at hp_pos))
  | @cons b _ q e =>
      let qT := transposeRev (A := A) (q.cons e)
      letI : Quiver n := toQuiver Aᵀ
      have hqT_pos : 0 < qT.length := by
        have : 0 < Nat.succ ((transposeRev (A := A) q).length) := Nat.succ_pos _
        simp [qT, transposeRev, Quiver.Path.length_comp, Quiver.Path.length_toPath]
      exact ⟨qT, hqT_pos⟩

theorem IsIrreducible.transpose_iff
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    IsIrreducible Aᵀ ↔ IsIrreducible A :=
  ⟨fun h ↦
    let hA_T_nonneg : ∀ i j, 0 ≤ (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    IsIrreducible.transpose hA_T_nonneg h,
   fun h ↦ IsIrreducible.transpose hA_nonneg h⟩

end Matrix
