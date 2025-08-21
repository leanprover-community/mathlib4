/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Quiver.Path.StronglyConnected
import Mathlib.Data.Matrix.Basic

/-!
# Irreducibility and primitivity of nonnegative real matrices via quivers

This file develops a graph-theoretic interface for studying nonnegative square matrices over `ℝ`
through the quiver formed by their strictly positive entries. The key theme is the equivalence
between positivity of suitable matrix powers and existence of directed paths in this quiver.

## Implementation notes

* The quiver uses strict positivity `0 < A i j` to define edges, while nonnegativity
  `0 ≤ A i j` is assumed globally when relating paths to positive entries in powers.

* Strong connectivity is expressed via `IsStronglyConnected n` in the quiver. This provides actual
  directed paths between any pair of vertices, which are then converted into positive entries of
  powers (and conversely) via the previous lemma.

* Some statements require `[DecidableEq n]` to expand matrix power entries and reason about finite
sums.

## Prerequisites and scope

* The development here is specialized to real matrices `Matrix n n ℝ`. Many statements would
  generalize to linearly ordered semifields or ordered rings with compatible algebraic and order
  structures; such generalizations are left as TODO.

## Tags

matrix, nonnegative, positive, power, quiver, graph, irreducible, primitive, strongly connected
-/

namespace Matrix

open scoped BigOperators

open Finset Quiver

variable {n : Type*} [Fintype n]

@[simp]
private lemma pow_nonneg [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; simp [one_apply]; by_cases h : i = j <;> simp [h]
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- The directed graph (quiver) associated with a matrix `A`,
with an edge `i ⟶ j` iff `0 < A i j`. -/
def toQuiver (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

/-- A matrix `A` is irreducible if it is entrywise nonnegative and
its quiver of positive entries (`toQuiver A`) is strongly connected. -/
def Irreducible (A : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (letI : Quiver n := toQuiver A; IsStronglyConnected n)

/-- A matrix `A` is primitive if it is entrywise nonnegative
and some positive power has all entries strictly positive. -/
def IsPrimitive [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∃ k, 0 < k ∧ ∀ i j, 0 < (A ^ k) i j

/-- If `A` is irreducible and `n>1` then every row has a positive entry. -/
lemma irreducible_no_zero_row
    (A : Matrix n n ℝ)
    (h_irr : Irreducible A) (h_dim : 1 < Fintype.card n) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_row ; push_neg at h_row
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j ↦ ⟨fun h ↦ (h_row j).not_gt h⟩
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_dim i
  obtain ⟨⟨p, _⟩⟩ := h_irr.2 i j
  have : False := by
    have aux : (∀ {v} (q : G.Path i v), v ≠ i → False) := by
      intro v q
      induction q with
      | nil =>
        intro hvi ; exact hvi rfl
      | cons r e ih =>
        cases r with
        | nil =>
            intro _
            exact (no_out _).false e
        | cons r' e' =>
            intro hvi ; simp_all only [isEmpty_Prop, ne_eq, imp_false, not_not, G]
    exact aux p hij
  exact this.elim

variable {A : Matrix n n ℝ}

open Classical in
private lemma sum_pos_of_mem {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  rw [Eq.symm (add_sum_erase s f ha_mem),  ]
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (fun x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [add_sum_erase s f ha_mem]; rw [propext (sum_pos_iff_of_nonneg h_nonneg)];
  exact Filter.frequently_principal.mp fun a_1 ↦ a_1 ha_mem ha_pos

-- Existence of positive element in positive sum
private lemma exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h; push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := fun a ha => le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by rw [sum_eq_zero_iff_of_nonneg h_nonneg]; exact h_zero
  linarith

private lemma mul_pos_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h_mul_pos
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · rintro rfl; simp_all only [le_refl, zero_mul, lt_self_iff_false]
    · rintro rfl; simp_all only [le_refl, mul_zero, lt_self_iff_false]
  · rintro ⟨ha_pos, hb_pos⟩; exact mul_pos ha_pos hb_pos

/--
For a matrix `A` with nonnegative entries, the `(i, j)`-entry of the `k`-th power `A ^ k`
is strictly positive if and only if there exists a path of length `k` from `i` to `j` in the
quiver associated to `A` via `toQuiver`. -/
theorem pow_entry_pos_iff_exists_path [DecidableEq n] (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := toQuiver A; 0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, nonempty_subtype]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq; exact ⟨letI := toQuiver A; Quiver.Path.nil, rfl⟩
      · exfalso; linarith [h_pos]
    · rintro ⟨p, hp⟩
      have h_eq : i = j := letI := toQuiver A; Quiver.Path.eq_of_length_zero p hp
      simp [h_eq]
  | succ m ih =>
    rw [pow_succ, mul_apply, nonempty_subtype]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ univ, 0 < (A ^ m) i l * A l j :=
        exists_mem_of_sum_pos h_pos fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j)
      rcases (mul_pos_iff_of_nonneg (pow_nonneg hA m i l) (hA l j)).mp hl_pos with ⟨h_Am, h_A⟩
      obtain ⟨⟨p, hp_len⟩⟩ := (ih i l).mp h_Am
      exact ⟨letI := toQuiver A; p.cons h_A, by
        subst hp_len
        simp_all only [mem_univ, nonempty_subtype, mul_pos_iff_of_pos_left, exists_apply_eq_apply,
          Path.length_cons]⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos
        exact sum_pos_of_mem
          (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j))
          b
          (Finset.mem_univ b)
          h_prod

/-- Irreducibility of a nonnegative matrix `A` is equivalent to entrywise positivity of some power:
between any two indices `i, j` there exists a positive integer `k` such that the `(i, j)`-entry
of `A ^ k` is strictly positive. -/
theorem irreducible_iff_exists_pow_pos [DecidableEq n] (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < k ∧ 0 < (A ^ k) i j := by
  constructor
  · intro h_irr i j
    rcases h_irr.2 i j with ⟨⟨p, hp_len⟩⟩
    letI := toQuiver A;
    use p.length, hp_len, by
      rw [pow_entry_pos_iff_exists_path hA]
      exact ⟨p, rfl⟩
  · intro h_exists
    constructor
    · exact hA
    · intro i j
      obtain ⟨k, hk_pos, hk_entry⟩ := h_exists i j
      letI := toQuiver A
      obtain ⟨⟨p, hp_len⟩⟩ := (pow_entry_pos_iff_exists_path hA k i j).mp hk_entry
      subst hp_len
      exact ⟨p, hk_pos⟩

/-- If a nonnegative square matrix `A` is primitive, then `A` is irreducible. -/
theorem IsPrimitive.to_Irreducible [DecidableEq n]
    (h_prim : IsPrimitive A) (hA : ∀ i j, 0 ≤ A i j) : Irreducible A := by
  rw [irreducible_iff_exists_pow_pos hA]
  intro i j
  obtain ⟨k, _hk_gt_zero, hk_pos⟩ := h_prim
  simp_all only [implies_true]
  obtain ⟨left, right⟩ := hk_pos
  apply Exists.intro
  · apply And.intro
    · exact left
    · simp_all only

/-- Irreducibility is invariant under transpose. -/
theorem Irreducible.transpose [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA : Irreducible A) : Irreducible Aᵀ := by
  have h_exists := (irreducible_iff_exists_pow_pos hA_nonneg).1 hA
  have h_iff := irreducible_iff_exists_pow_pos (fun i j => hA_nonneg j i)
  apply h_iff.mpr
  intro i j
  obtain ⟨k, hk_pos, hk⟩ := h_exists j i
  use k, hk_pos
  erw [← transpose_pow]
  exact hk

end Matrix
