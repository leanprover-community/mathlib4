/-
Copyright (c) 2021 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

#align_import imo.imo1994_q1 from "leanprover-community/mathlib"@"308826471968962c6b59c7ff82a22757386603e3"

/-!
# IMO 1994 Q1

Let `m` and `n` be two positive integers.
Let `a₁, a₂, ..., aₘ` be `m` different numbers from the set `{1, 2, ..., n}`
such that for any two indices `i` and `j` with `1 ≤ i ≤ j ≤ m` and `aᵢ + aⱼ ≤ n`,
there exists an index `k` such that `aᵢ + aⱼ = aₖ`.
Show that `(a₁+a₂+...+aₘ)/m ≥ (n+1)/2`

# Sketch of solution

We can order the numbers so that `a₁ ≤ a₂ ≤ ... ≤ aₘ`.
The key idea is to pair the numbers in the sum and show that `aᵢ + aₘ₊₁₋ᵢ ≥ n+1`.
Indeed, if we had `aᵢ + aₘ₊₁₋ᵢ ≤ n`, then `a₁ + aₘ₊₁₋ᵢ, a₂ + aₘ₊₁₋ᵢ, ..., aᵢ + aₘ₊₁₋ᵢ`
would be `m` elements of the set of `aᵢ`'s all larger than `aₘ₊₁₋ᵢ`, which is impossible.
-/


open scoped BigOperators

open Finset

namespace Imo1994Q1

theorem tedious (m : ℕ) (k : Fin (m + 1)) : m - (m + (m + 1 - ↑k)) % (m + 1) = ↑k := by
  cases' k with k hk
  rw [Nat.lt_succ_iff, le_iff_exists_add] at hk
  rcases hk with ⟨c, rfl⟩
  have : k + c + (k + c + 1 - k) = c + (k + c + 1) := by
    simp only [add_assoc, add_tsub_cancel_left, add_left_comm]
  rw [Fin.val_mk, this, Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.add_sub_cancel]
  linarith
#align imo1994_q1.tedious Imo1994Q1.tedious

end Imo1994Q1

open Imo1994Q1

theorem imo1994_q1 (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : A.card = m + 1)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ n)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) :
    (m + 1) * (n + 1) ≤ 2 * ∑ x in A, x := by
  set a := orderEmbOfFin A hm
  -- We sort the elements of `A`
  have ha : ∀ i, a i ∈ A := fun i => orderEmbOfFin_mem A hm i
  set rev := Equiv.subLeft (Fin.last m)
  -- `i ↦ m-i`
  -- We reindex the sum by fin (m+1)
  have : ∑ x in A, x = ∑ i : Fin (m + 1), a i := by
    convert sum_image (α := ℕ) (β := ℕ) fun x _ y _ => (OrderEmbedding.eq_iff_eq a).1
    rw [← coe_inj]; simp
  rw [this]; clear this
  -- The main proof is a simple calculation by rearranging one of the two sums
  suffices hpair : ∀ k ∈ univ, a k + a (rev k) ≥ n + 1
  calc
    2 * ∑ i : Fin (m + 1), a i = ∑ i : Fin (m + 1), a i + ∑ i : Fin (m + 1), a i := two_mul _
    _ = ∑ i : Fin (m + 1), a i + ∑ i : Fin (m + 1), a (rev i) := by rw [Equiv.sum_comp rev]
    _ = ∑ i : Fin (m + 1), (a i + a (rev i)) := sum_add_distrib.symm
    _ ≥ ∑ i : Fin (m + 1), (n + 1) := (sum_le_sum hpair)
    _ = (m + 1) * (n + 1) := by rw [sum_const, card_fin, Nat.nsmul_eq_mul]
  -- It remains to prove the key inequality, by contradiction
  rintro k -
  by_contra! h : a k + a (rev k) < n + 1
  -- We exhibit `k+1` elements of `A` greater than `a (rev k)`
  set f : Fin (m + 1) ↪ ℕ :=
    ⟨fun i => a i + a (rev k), by
      apply injective_of_le_imp_le
      intro i j hij
      rwa [add_le_add_iff_right, a.map_rel_iff] at hij ⟩
  -- Proof that the `f i` are greater than `a (rev k)` for `i ≤ k`
  have hf : map f (Icc 0 k) ⊆ map a.toEmbedding (Ioc (rev k) (Fin.last m)) := by
    intro x hx
    simp only [Equiv.subLeft_apply] at h
    simp only [mem_map, mem_Icc, mem_Ioc, Fin.zero_le, true_and_iff, Equiv.subLeft_apply,
      Function.Embedding.coeFn_mk, exists_prop, RelEmbedding.coe_toEmbedding] at hx ⊢
    rcases hx with ⟨i, ⟨hi, rfl⟩⟩
    have h1 : a i + a (Fin.last m - k) ≤ n := by linarith only [h, a.monotone hi]
    have h2 : a i + a (Fin.last m - k) ∈ A := hadd _ (ha _) _ (ha _) h1
    rw [← mem_coe, ← range_orderEmbOfFin A hm, Set.mem_range] at h2
    cases' h2 with j hj
    refine' ⟨j, ⟨_, Fin.le_last j⟩, hj⟩
    rw [← a.strictMono.lt_iff_lt, hj]
    simpa using (hrange (a i) (ha i)).1
  -- A set of size `k+1` embed in one of size `k`, which yields a contradiction
  simpa [Fin.coe_sub, tedious] using card_le_of_subset hf
#align imo1994_q1 imo1994_q1
