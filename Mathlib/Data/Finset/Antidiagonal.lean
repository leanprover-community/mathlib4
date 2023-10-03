/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval

/-! # Antidiagonal with values in general types

Let `n : μ`, where `μ` is a canonically ordered add monoid with locally finite order.

* For `s : Finset ι`, we define `Finset.Pi.antidiagonal s n` as the `Finset (ι → μ)`
of functions with support in `s` whose sum is equal to `n`.

* We define `Finset.antidiagonal n : Finset (μ × μ)` of pairs adding to `n`.

These definitions generalize `Finset.Nat.antidiagonal` and `Finsupp.antidiagonal`
which are defined in `Mathlib.Data.Finset.NatAntidiagonal`
and `Mathlib.Data.Finsupp.Antidiagonal` and we make the comparisons there.

This definition does not exactly match with that of `Multiset.antidiagonal` which is
defined in `Mathlib.Data.Multiset.Antidiagonal`, because of the multiplicities.
Indeed, by counting multiplicities, `Multiset α` is equivalent to `α →₀ ℕ`,
but `Finset.antidiagonal` and `Multiset.antidiagonal` will return different objects.
For example, for `s : Multiset ℕ := {0,0,0}`, `Multiset.antidiagonal s` has 8 elements
but `Finset.antidiagonal s` has only 4.

-- def s : Multiset ℕ := {0, 0, 0}
-- #eval (Finset.antidiagonal s).card -- 4
-- #eval Multiset.card (Multiset.antidiagonal s) -- 8

This is mostly taken from a mathlib3 file of Bhavik Mehta,
https://leanprover-community.github.io/mathlib_docs/wiedijk_100_theorems/partition.html
-/

open scoped BigOperators

open Finset Function

variable {μ : Type _} [CanonicallyOrderedAddMonoid μ] [LocallyFiniteOrder μ] [DecidableEq μ]

variable {ι : Type _} [DecidableEq ι] [DecidableEq (ι → μ)]

namespace Finset

/-- The Finset of pairs of elements of `μ` with sum `n` -/
def antidiagonal (n : μ) : Finset (μ × μ) :=
  Finset.filter (fun uv => uv.fst + uv.snd = n) (Finset.product (Iic n) (Iic n))
#align finset.antidiagonal Finset.antidiagonal

@[simp]
theorem mem_antidiagonal (n : μ) (a : μ × μ) : a ∈ antidiagonal n ↔ a.fst + a.snd = n := by
  simp only [antidiagonal, Prod.forall, mem_filter, and_iff_right_iff_imp]
  intro h; rw [← h]
  erw [mem_product, mem_Iic, mem_Iic]
  exact ⟨le_self_add, le_add_self⟩

/-- The Finset of functions `ι → μ` whose support is contained in `s`
  and whose sum is `n` -/
def Pi.antidiagonal (s : Finset ι) (n : μ) : Finset (ι → μ) :=
  Finset.filter (fun f => s.sum f = n)
    ((s.pi fun _ => Iic n).map
      ⟨fun f i => if h : i ∈ s then f i h else 0,
        fun f g h => by ext i hi; simpa only [dif_pos hi] using congr_fun h i⟩)

@[simp]
theorem Pi.mem_antidiagonal (s : Finset ι) (n : μ) (f : ι → μ) :
    f ∈ Pi.antidiagonal s n ↔ s.sum f = n ∧ ∀ (i) (_ : i ∉ s), f i = 0 := by
  rw [Pi.antidiagonal, mem_filter, and_comm, and_congr_right]
  intro h
  simp only [mem_map, exists_prop, Function.Embedding.coeFn_mk, mem_pi]
  constructor
  · rintro ⟨_, _, rfl⟩ _ hi
    dsimp only
    rw [dif_neg hi]
  · intro hf
    refine' ⟨fun i _ => f i, fun i hi => _, _⟩
    · rw [mem_Iic, ← h]
      apply single_le_sum _ hi
      simp only [zero_le, implies_true]
    · ext x
      dsimp only
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm]
      exact hf x

theorem Pi_antidiagonal_equiv_antidiagonal (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (Pi.antidiagonal univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk, ←
    Equiv.eq_symm_apply]
  simp [Pi.mem_antidiagonal, add_comm, mem_antidiagonal]

theorem Pi.antidiagonal_zero (s : Finset ι) :
    Pi.antidiagonal s (0 : μ) = {0} := by
  ext f
  rw [Pi.mem_antidiagonal, mem_singleton, sum_eq_zero_iff, ← forall_and, funext_iff]
  apply forall_congr'
  intro i
  simp only [← or_imp, em (i ∈ s), forall_true_left, Pi.zero_apply]

theorem Pi.antidiagonal_empty (n : μ) :
    Pi.antidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  ext f
  rw [Pi.mem_antidiagonal]
  simp only [sum_empty, not_mem_empty, not_false_iff, forall_true_left]
  split_ifs with hn
  simp only [hn, mem_singleton, funext_iff, eq_self_iff_true, true_and_iff, Pi.zero_apply]
  simp only [not_mem_empty, iff_false_iff]
  intro h'; exact hn h'.1.symm

theorem Pi.antidiagonal_insert (n : μ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    Pi.antidiagonal (insert a s) n =
      (Finset.antidiagonal n).biUnion fun p : μ × μ =>
        (Pi.antidiagonal s p.snd).image fun f => Function.update f a p.fst := by
  ext f
  rw [Pi.mem_antidiagonal, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, mem_antidiagonal, Prod.exists]
    use f a, s.sum f
    constructor
    · exact (Finset.mem_antidiagonal (f a + ∑ x in s, f x) (f a, Finset.sum s f)).mpr rfl
    rw [mem_image]
    use Function.update f a 0
    constructor
    · rw [Pi.mem_antidiagonal s (s.sum f)]
      constructor
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_apply]; rw [if_neg]; intro hia; apply h; rw [← hia]; exact hi
      intro i hi; rw [Function.update_apply]; split_ifs with hia
      rfl
      apply h₁; simp only [mem_insert, not_or]; exact ⟨hia, hi⟩
    · ext i
      rw [Function.update_apply (update f a 0), Function.update_apply]
      split_ifs with hia
      rw [hia]
      rfl
  · simp only [mem_insert, Finset.mem_antidiagonal, mem_image, exists_prop,
      Prod.exists, forall_exists_index, and_imp, mem_antidiagonal]
    rintro d e rfl g hg hg' rfl
    constructor
    · simp only [Function.update_same]
      apply congr_arg₂ _ rfl
      rw [← hg]
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_noteq _]
      intro hia; apply h; simpa only [hia] using hi
    · intro i hi; rw [not_or] at hi
      rw [Function.update_noteq hi.1]
      exact hg' i hi.2

end Finset
