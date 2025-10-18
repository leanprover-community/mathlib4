/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Filter.Basic
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
*   `Matrix.Irreducible A`: A matrix `A` is defined as irreducible if it is entrywise nonnegative
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
*   `IsPrimitive.to_Irreducible`: Proves that a primitive matrix is also irreducible, as stated in
    Seneta (p.14).
*   `Irreducible.transpose`: Shows that the irreducibility property is preserved under
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

@[simp]
lemma pow_nonneg [IsOrderedRing R] [DecidableEq n] {A : Matrix n n R}
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; simp [one_apply]; by_cases h : i = j <;> simp [h]
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- The directed graph (quiver) associated with a matrix `A`,
with an edge `i ⟶ j` iff `0 < A i j`. -/
def toQuiver (A : Matrix n n R) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

/-- A matrix `A` is irreducible if it is entrywise nonnegative and
its quiver of positive entries (`toQuiver A`) is strongly connected. -/
def Irreducible (A : Matrix n n R) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ @IsSStronglyConnected n (toQuiver A)

/-- A matrix `A` is primitive if it is entrywise nonnegative
and some positive power has all entries strictly positive. -/
def IsPrimitive [DecidableEq n] (A : Matrix n n R) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∃ k, 0 < k ∧ ∀ i j, 0 < (A ^ k) i j

variable {A : Matrix n n R}

/-- If `A` is irreducible and `n>1` then every row has a positive entry. -/
lemma Irreducible.no_zero_row
    (h_irr : Irreducible A) (h_dim : 1 < Fintype.card n) (i : n) :
    ∃ j, 0 < A i j := by
  letI : Quiver n := toQuiver A
  by_contra h_row
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e⟩⟩
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_dim i
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

lemma sum_pos_of_mem [IsOrderedRing R] {α : Type*} {s : Finset α} {f : α → R}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  classical
  rw [Eq.symm (add_sum_erase s f ha_mem),  ]
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (fun x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [add_sum_erase s f ha_mem]; rw [propext (sum_pos_iff_of_nonneg h_nonneg)];
  exact Filter.frequently_principal.mp fun a_1 ↦ a_1 ha_mem ha_pos

-- Existence of positive element in positive sum
lemma exists_mem_of_sum_pos [IsOrderedRing R] {α : Type*} {s : Finset α} {f : α → R}
    (h_pos : 0 < ∑ a ∈ s, f a) (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h; push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := fun a ha => le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by rw [sum_eq_zero_iff_of_nonneg h_nonneg]; exact h_zero
  simp_all only [sum_const_zero, lt_self_iff_false]

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
    simp only [pow_zero, one_apply, nonempty_subtype]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq; exact ⟨letI := toQuiver A; Quiver.Path.nil, rfl⟩
      · exfalso; simp_all only [lt_self_iff_false]
    · rintro ⟨p, hp⟩
      have h_eq : i = j := letI := toQuiver A; Quiver.Path.eq_of_length_zero p hp
      simp [h_eq]
  | succ m ih =>
    rw [pow_succ, mul_apply, nonempty_subtype]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ univ, 0 < (A ^ m) i l * A l j :=
        exists_mem_of_sum_pos h_pos fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j)
      have hAm_nonneg : 0 ≤ (A ^ m) i l := pow_nonneg hA m i l
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
        simp_all only [mem_univ, nonempty_subtype,
          exists_apply_eq_apply, Path.length_cons]⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos
        exact sum_pos_of_mem
          (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j)) b (Finset.mem_univ b) h_prod

/-- Irreducibility of a nonnegative matrix `A` is equivalent to entrywise positivity of some
power: between any two indices `i, j` there exists a positive integer `k` such that the
`(i, j)`-entry of `A ^ k` is strictly positive. -/
theorem irreducible_iff_exists_pow_pos
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < k ∧ 0 < (A ^ k) i j := by
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
theorem IsPrimitive.to_Irreducible
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (h_prim : IsPrimitive A) : Irreducible A := by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  constructor
  · exact h_nonneg
  · unfold IsSStronglyConnected
    intro i j
    letI : Quiver n := toQuiver A
    have h_entry : 0 < (A ^ k) i j := hk_all i j
    have ⟨⟨p, hp⟩⟩ : Nonempty {p : Path i j // p.length = k} := by
      rw [← pow_entry_pos_iff_exists_path h_nonneg k i j]
      exact h_entry
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

/-- The reversal along transpose preserves the length of the path. -/
@[simp]
lemma transposeRev_length
    {n R : Type*} [Ring R] [LinearOrder R] {A : Matrix n n R} {i j : n}
    (p : @Quiver.Path n (toQuiver A) i j) :
    (@Quiver.Path.length n (toQuiver Aᵀ) _ _ (transposeRev p)) =
    @Quiver.Path.length n (toQuiver A) _ _ p := by
  letI : Quiver n := toQuiver A
  induction p with
  | nil => rfl
  | @cons b c q e ih =>
    have eT : @Quiver.Hom n (toQuiver Aᵀ) c b := by
      change 0 < (Aᵀ) c b
      simpa [Matrix.transpose_apply] using e
    letI : Quiver n := toQuiver Aᵀ
    simp only [transposeRev, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    norm_num; ring_nf; simpa

/-- If `A` is entrywise nonnegative and some power has a positive `(j,i)` entry,
then the transpose has a positive `(i,j)` entry in the same power. -/
lemma exists_pow_pos_transpose_of_exists_pow_pos
    {n R : Type*} [Fintype n] [Ring R] [LinearOrder R]
    [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    {A : Matrix n n R} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {i j : n} :
    (∃ k, 0 < k ∧ 0 < (A ^ k) j i) → (∃ k, 0 < k ∧ 0 < (Aᵀ ^ k) i j) := by
  rintro ⟨k, hk_pos, hk_pos_entry⟩
  letI : Quiver n := toQuiver A
  obtain ⟨⟨p, hp_len⟩⟩ :=
    (pow_entry_pos_iff_exists_path (A := A) hA_nonneg k j i).mp hk_pos_entry
  let q := transposeRev (A := A) p
  letI : Quiver n := toQuiver Aᵀ
  have hq_len :
      (by exact q.length) = k := by
    have h := transposeRev_length (A := A) (i := j) (j := i) p
    calc (by exact q.length) = (by letI : Quiver n := toQuiver A; exact p.length) := h
      _ = k := hp_len
  have hT_nonneg : ∀ x y, 0 ≤ (Aᵀ) x y := fun x y => by
    simpa [Matrix.transpose_apply] using hA_nonneg y x
  have hposT : 0 < (Aᵀ ^ k) i j := by
    letI : Quiver n := toQuiver Aᵀ
    have hw : Nonempty {p' : Quiver.Path i j // p'.length = k} := ⟨⟨q, hq_len⟩⟩
    exact (pow_entry_pos_iff_exists_path (A := Aᵀ) hT_nonneg k i j).2 hw
  exact ⟨k, hk_pos, hposT⟩

/-- Irreducibility is invariant under transpose. -/
theorem Irreducible.transpose
    [DecidableEq n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA : Irreducible A) : Irreducible Aᵀ := by
  have hA_T_nonneg : ∀ i j, 0 ≤ (Aᵀ) i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA_nonneg j i
  have h_exists : ∀ i j, ∃ k, 0 < k ∧ 0 < (A ^ k) i j :=
    (irreducible_iff_exists_pow_pos (A := A) hA_nonneg).mp hA
  have h_existsT : ∀ i j, ∃ k, 0 < k ∧ 0 < (Aᵀ ^ k) i j := by
    intro i j
    rcases h_exists j i with ⟨k, hk_pos, hk⟩
    exact exists_pow_pos_transpose_of_exists_pow_pos (A := A) hA_nonneg ⟨k, hk_pos, hk⟩
  exact (irreducible_iff_exists_pow_pos (A := Aᵀ) hA_T_nonneg).mpr h_existsT

end Matrix
