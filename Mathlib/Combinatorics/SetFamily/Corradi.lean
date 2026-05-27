/-
Copyright (c) 2026 Andrew Zitek-Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada, Ziyi Guan, Ignacio Manzur
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Corrádi's intersection lemma

If `A₁, …, Aₘ ⊆ A` each have cardinality `a` and pairwise intersections of
cardinality at most `b`, then `m · (a² − b·|A|) ≤ |A| · (a − b)`.
This is Corrádi (1969); see Jukna, *Extremal Combinatorics*, Lemma 5.5.

The proof is double-counting followed by Cauchy–Schwarz on the cover-count
function `x ↦ #{i | x ∈ Aᵢ}`.

## Main results

* `Finset.corradi_mul_le`: the underlying integer inequality
  `m² · a² + m · N · b ≤ m · N · a + m² · N · b`, unconditional.
* `Finset.corradi_card_le_real`: the standard ratio form
  `m · (a² − b·N) ≤ N · (a − b)`, stated in `ℝ` to avoid `Nat`-subtraction.

## References

* K. Corrádi, *Mat. Lapok* 20 (1969).
* S. Jukna, *Extremal Combinatorics* (Springer, 2011), Lemma 5.5.
-/

@[expose] public section

namespace Finset

variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-- The number of indices `i` such that `x ∈ As i`. -/
def coverCount (As : ι → Finset α) (x : α) : ℕ :=
  #(univ.filter fun i => x ∈ As i)

variable {A : Finset α} {As : ι → Finset α} {a b : ℕ}

/-! ### Double-counting identities -/

/-- Summing `coverCount` over `A` equals the total family size. -/
lemma sum_coverCount_eq_sum_card (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, coverCount As x = ∑ i, #(As i) := by
  classical
  simp_rw [coverCount, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (h_sub i)]

lemma sum_coverCount_eq_card_mul (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a) :
    ∑ x ∈ A, coverCount As x = Fintype.card ι * a := by
  rw [sum_coverCount_eq_sum_card h_sub, sum_congr rfl (fun i _ => h_size i)]
  rw [sum_const, card_univ, smul_eq_mul]

/-- Sum of squared cover-counts equals the total pairwise-intersection size
(diagonal included). -/
lemma sum_coverCount_sq_eq_sum_inter_card (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, (coverCount As x) ^ 2 = ∑ p : ι × ι, #(As p.1 ∩ As p.2) := by
  classical
  have hpow (x : α) :
      (coverCount As x) ^ 2 = ∑ p : ι × ι, if x ∈ As p.1 ∧ x ∈ As p.2 then (1 : ℕ) else 0 := by
    simp only [coverCount]
    rw [sq, card_eq_sum_ones, sum_filter, sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_congr rfl fun p _ => ?_
    by_cases h₁ : x ∈ As p.1 <;> by_cases h₂ : x ∈ As p.2 <;> simp [h₁, h₂]
  simp_rw [hpow]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, ← card_eq_sum_ones]
  congr 1
  ext x
  simp only [mem_filter, mem_inter]
  exact ⟨fun ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h_sub _ h₁, h₁, h₂⟩⟩

/-- Diagonal contributes `m · a`, off-diagonal at most `m(m-1) · b`. -/
lemma sum_inter_card_le (h_size : ∀ i, #(As i) = a)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b) :
    ∑ p : ι × ι, #(As p.1 ∩ As p.2)
      ≤ Fintype.card ι * a + Fintype.card ι * (Fintype.card ι - 1) * b := by
  classical
  rw [← univ_product_univ, sum_product]
  have h_inner : ∀ i : ι, ∑ j, #(As i ∩ As j) ≤ a + (Fintype.card ι - 1) * b := by
    intro i
    rw [← add_sum_erase _ _ (mem_univ i), inter_self, h_size]
    refine Nat.add_le_add_left ?_ a
    calc ∑ j ∈ univ.erase i, #(As i ∩ As j)
        ≤ ∑ _j ∈ univ.erase i, b :=
          sum_le_sum fun j hj => h_pairwise i j (ne_of_mem_erase hj).symm
      _ = (Fintype.card ι - 1) * b := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, smul_eq_mul]
  calc ∑ i, ∑ j, #(As i ∩ As j)
      ≤ ∑ _i : ι, (a + (Fintype.card ι - 1) * b) := sum_le_sum fun i _ => h_inner i
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_add, ← mul_assoc]

/-! ### Main results -/

/-- **Corrádi's lemma (underlying integer form).**
Suppose `A₁, …, Aₘ ⊆ A` each have size `a` with pairwise intersections of
size at most `b`. With `m := |ι|` and `N := |A|`:
`m² · a² + m · N · b ≤ m · N · a + m² · N · b`.

This is the unconditional double-counting + Cauchy–Schwarz inequality;
the standard ratio form `m · (a² − b·N) ≤ N · (a − b)` follows over `ℝ`
in `corradi_card_le_real`. -/
theorem corradi_mul_le (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b) :
    (Fintype.card ι) ^ 2 * a ^ 2 + Fintype.card ι * #A * b ≤
      Fintype.card ι * #A * a + (Fintype.card ι) ^ 2 * #A * b := by
  have hCS : (Fintype.card ι * a) ^ 2
      ≤ #A * (Fintype.card ι * a + Fintype.card ι * (Fintype.card ι - 1) * b) :=
    calc (Fintype.card ι * a) ^ 2
        = (∑ x ∈ A, coverCount As x) ^ 2 := by
          rw [sum_coverCount_eq_card_mul h_sub h_size]
      _ ≤ #A * ∑ x ∈ A, (coverCount As x) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ #A * (Fintype.card ι * a + Fintype.card ι * (Fintype.card ι - 1) * b) := by
          rw [sum_coverCount_sq_eq_sum_inter_card h_sub]
          exact Nat.mul_le_mul_left _ (sum_inter_card_le h_size h_pairwise)
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hm | hm
  · simp [hm]
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 1 :=
    ⟨Fintype.card ι - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [hk] at hCS ⊢
  simp only [Nat.add_sub_cancel] at hCS
  nlinarith [hCS, sq_nonneg k, Nat.zero_le a, Nat.zero_le b, Nat.zero_le (#A)]

/-- **Corrádi's lemma, real-valued ratio form.**
Under `b ≤ a`, `m · (a² − b·N) ≤ N · (a − b)` as real numbers. -/
theorem corradi_card_le_real (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b)
    (h_ba : b ≤ a) :
    (Fintype.card ι : ℝ) * ((a : ℝ) ^ 2 - (b : ℝ) * #A) ≤ (#A : ℝ) * ((a : ℝ) - b) := by
  have key_real : ((Fintype.card ι : ℝ)) ^ 2 * (a : ℝ) ^ 2 + (Fintype.card ι) * #A * b ≤
      (Fintype.card ι : ℝ) * #A * a + ((Fintype.card ι : ℝ)) ^ 2 * #A * b := by
    exact_mod_cast corradi_mul_le h_sub h_size h_pairwise (a := a) (b := b)
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hm | hm
  · simp only [hm, Nat.cast_zero, zero_mul]
    have : (0 : ℝ) ≤ (a : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast h_ba)
    positivity
  · have hmR : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hm
    nlinarith [key_real, hmR, sq_nonneg ((Fintype.card ι : ℝ) - 1)]

end Finset
