/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Sub.Defs

/-! # Partial HasAntidiagonal for functions with finite support

Let `μ` be an AddCommMonoid.

In `Mathlib.Data.Finset.Antidiagonal` is defined a TypeClass
`HasAntidiagonal μ` which provides a function `μ → Finset (μ × μ)
which maps `n : μ` to a `Finset` of pairs `(a,b)`
such that `a + b = n`.

These functions apply to (ι →₀ ℕ), more generally to (ι →₀ μ)
under the additional assumption `OrderedSub μ` that make it
a canonically ordered add monoid.
In fact, we just need an AddMonoid with a compatible order,
finite Iic, such that if a + b = n, then a, b ≤ n,
and any other bound would be OK.

In this file, we provide an analogous definition for ι → μ,
with an explicit finiteness conditions on the support

* For `s : Finset ι`, we define `Finset.piAntidiagonal s n` as the `Finset (ι → μ)`
of functions with support in `s` whose sum is equal to `n`.

-/

namespace Finset

open scoped BigOperators

open Function

variable {μ : Type*}
  [CanonicallyOrderedAddCommMonoid μ]
  [LocallyFiniteOrder μ] [DecidableEq μ]

variable {ι : Type*} [DecidableEq ι]

/-- The Finset of functions `ι → μ` whose support is contained in `s : Finset ι`
  and whose sum is `n` -/
def piAntidiagonal (s : Finset ι) (n : μ) : Finset (ι → μ) :=
  Finset.filter (fun f => s.sum f = n)
    ((s.pi fun _ => Iic n).map
      ⟨fun f i => if h : i ∈ s then f i h else 0,
        fun f g h => by ext i hi; simpa only [dif_pos hi] using congr_fun h i⟩)

@[simp]
theorem mem_piAntidiagonal (s : Finset ι) (n : μ) (f : ι → μ) :
    f ∈ piAntidiagonal s n ↔ s.sum f = n ∧ ∀ (i) (_ : i ∉ s), f i = 0 := by
  rw [piAntidiagonal, mem_filter, and_comm, and_congr_right]
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

def piAntidiagonal' (s : Finset ι) : HasAntidiagonal
  { f : ι → μ // f.support ≤ s } where
  }


-- Should this be promoted into a HasAntidiagonal instance?
theorem piAntidiagonal_equiv_antidiagonal [HasAntidiagonal μ] (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (piAntidiagonal univ n) =
      Finset.HasAntidiagonal.antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding,
    Function.Embedding.coeFn_mk, ← Equiv.eq_symm_apply]
  simp [mem_piAntidiagonal, add_comm, Finset.HasAntidiagonal.mem_antidiagonal]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff, ← forall_and, funext_iff]
  apply forall_congr'
  intro i
  simp only [← or_imp, em (i ∈ s), forall_true_left, Pi.zero_apply]

theorem piAntidiagonal_empty (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [sum_empty, not_mem_empty, not_false_iff, forall_true_left]
  split_ifs with hn
  simp only [hn, mem_singleton, funext_iff, eq_self_iff_true, true_and_iff, Pi.zero_apply]
  simp only [not_mem_empty, iff_false_iff]
  intro h'; exact hn h'.1.symm

theorem piAntidiagonal_insert [HasAntidiagonal μ] [DecidableEq (ι → μ)]
    (n : μ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    piAntidiagonal (insert a s) n =
      (Finset.HasAntidiagonal.antidiagonal n).biUnion
        fun p : μ × μ =>
          (piAntidiagonal s p.snd).image (fun f => Function.update f a p.fst) := by
  ext f
  rw [mem_piAntidiagonal, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, mem_piAntidiagonal, Prod.exists]
    use f a, s.sum f
    constructor
    · rw [mem_antidiagonal]
    rw [mem_image]
    use Function.update f a 0
    constructor
    · rw [mem_piAntidiagonal s (s.sum f)]
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
  · simp only [mem_insert, Finset.HasAntidiagonal.mem_antidiagonal, mem_image, exists_prop,
      Prod.exists, forall_exists_index, and_imp, mem_piAntidiagonal]
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
