/-
Copyright (c) 2026 Andrew Zitek-Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada, Ziyi Guan, Ignacio Manzur.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Corrádi's intersection lemma

If `A₁, …, Aₘ ⊆ A` each have cardinality `a` and pairwise intersections of
cardinality at most `b`, then `m · (a² − b·|A|) ≤ |A| · (a − b)`.
This is Corrádi (1969); see Jukna, *Extremal Combinatorics*, Lemma 5.5.

The proof is double-counting followed by Cauchy–Schwarz on the cover-count
function `x ↦ #{i | x ∈ Aᵢ}`.

## Main results

* `Finset.corradi_mul_le`: `m² a² + m N b ≤ m N a + m² N b`, unconditional.
* `Finset.corradi_mul_le_of_card_ge`: lower-bound variant
  `m² a² ≤ m N² + m (m−1) N b`, used to derive the classical Johnson bound
  on list-decoding radius in MDS codes.
* `Finset.corradi_card_le`: `m · (a² − bN) ≤ N · (a − b)` (integer form,
  assuming `b · N ≤ a²` and `b ≤ a`).
* `Finset.corradi_card_le_real`: the same ratio bound, stated in `ℝ`.

## References

* K. Corrádi, *Mat. Lapok* 20 (1969).
* S. Jukna, *Extremal Combinatorics* (Springer, 2011), Lemma 5.5.
* S. M. Johnson, "A new upper bound for error-correcting codes",
  *IEEE Trans. Inform. Theory* 8 (1962) — the prototypical coding-theoretic
  application.
-/

namespace Finset

variable {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The number of indices `i` such that `x ∈ As i`. -/
def coverCount (As : ι → Finset α) (x : α) : ℕ :=
  #(univ.filter fun i => x ∈ As i)

variable {A : Finset α} {As : ι → Finset α} {a b : ℕ}

/-! ### Double-counting identities -/

omit [DecidableEq ι] in
/-- Summing `coverCount` over `A` equals the total family size. -/
lemma sum_coverCount_eq_sum_card (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, coverCount As x = ∑ i, #(As i) := by
  simp_rw [coverCount, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (h_sub i)]

omit [DecidableEq ι] in
lemma sum_coverCount_eq_card_mul (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a) :
    ∑ x ∈ A, coverCount As x = Fintype.card ι * a := by
  rw [sum_coverCount_eq_sum_card h_sub, sum_congr rfl (fun i _ => h_size i)]
  rw [sum_const, card_univ, smul_eq_mul]

omit [DecidableEq ι] in
/-- Sum of squared cover-counts equals the total pairwise-intersection size
(diagonal included). -/
lemma sum_coverCount_sq_eq_sum_inter_card (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, (coverCount As x) ^ 2 = ∑ p : ι × ι, #(As p.1 ∩ As p.2) := by
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

/-- Variant without the equal-size hypothesis: diagonal bounded by `|A|` per set. -/
lemma sum_inter_card_le_of_subset (h_sub : ∀ i, As i ⊆ A)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b) :
    ∑ p : ι × ι, #(As p.1 ∩ As p.2)
      ≤ Fintype.card ι * #A + Fintype.card ι * (Fintype.card ι - 1) * b := by
  rw [← univ_product_univ, sum_product]
  have h_inner : ∀ i : ι, ∑ j, #(As i ∩ As j) ≤ #A + (Fintype.card ι - 1) * b := by
    intro i
    rw [← add_sum_erase _ _ (mem_univ i), inter_self]
    refine Nat.add_le_add (card_le_card (h_sub i)) ?_
    calc ∑ j ∈ univ.erase i, #(As i ∩ As j)
        ≤ ∑ _j ∈ univ.erase i, b :=
          sum_le_sum fun j hj => h_pairwise i j (ne_of_mem_erase hj).symm
      _ = (Fintype.card ι - 1) * b := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, smul_eq_mul]
  calc ∑ i, ∑ j, #(As i ∩ As j)
      ≤ ∑ _i : ι, (#A + (Fintype.card ι - 1) * b) := sum_le_sum fun i _ => h_inner i
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_add, ← mul_assoc]

/-! ### Main results -/

/-- **Corrádi's lemma (integer, unconditional form).**
Suppose `A₁, …, Aₘ ⊆ A` each have size `a` with pairwise intersections of
size at most `b`. With `m := |ι|` and `N := |A|`:
`m² · a² + m · N · b ≤ m · N · a + m² · N · b`. -/
theorem corradi_mul_le (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b) :
    (Fintype.card ι) ^ 2 * a ^ 2 + Fintype.card ι * #A * b ≤
      Fintype.card ι * #A * a + (Fintype.card ι) ^ 2 * #A * b := by
  set m := Fintype.card ι
  set N := #A
  have hCS : (m * a) ^ 2 ≤ N * (m * a + m * (m - 1) * b) :=
    calc (m * a) ^ 2
        = (∑ x ∈ A, coverCount As x) ^ 2 := by
          rw [sum_coverCount_eq_card_mul h_sub h_size]
      _ ≤ #A * ∑ x ∈ A, (coverCount As x) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ N * (m * a + m * (m - 1) * b) := by
          rw [sum_coverCount_sq_eq_sum_inter_card h_sub]
          exact Nat.mul_le_mul_left N (sum_inter_card_le h_size h_pairwise)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · have h_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc m ^ 2 * a ^ 2 + m * N * b
        = (m * a) ^ 2 + m * N * b := by ring
      _ ≤ N * (m * a + m * (m - 1) * b) + m * N * b := by linarith [hCS]
      _ = m * N * a + m * N * b * (m - 1 + 1) := by ring
      _ = m * N * a + m * N * b * m := by rw [h_succ]
      _ = m * N * a + m ^ 2 * N * b := by ring

/-- **Corrádi's lemma, lower-bound variant.**
When the `As i` only satisfy `a ≤ #(As i)` (rather than equality) and lie
inside a common `A`, the inequality becomes the slightly looser
`m² · a² ≤ m · N² + m · (m − 1) · N · b`. This is the form used in the
classical Johnson bound on list-decoding radius. -/
theorem corradi_mul_le_of_card_ge (h_sub : ∀ i, As i ⊆ A)
    (h_ge : ∀ i, a ≤ #(As i))
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b) :
    (Fintype.card ι) ^ 2 * a ^ 2 ≤
      Fintype.card ι * #A ^ 2 + Fintype.card ι * (Fintype.card ι - 1) * #A * b := by
  set m := Fintype.card ι
  set N := #A
  have hS : m * a ≤ ∑ x ∈ A, coverCount As x := by
    rw [sum_coverCount_eq_sum_card h_sub]
    calc m * a = ∑ _i : ι, a := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ ∑ i, #(As i) := sum_le_sum fun i _ => h_ge i
  calc m ^ 2 * a ^ 2
      = (m * a) ^ 2 := by ring
    _ ≤ (∑ x ∈ A, coverCount As x) ^ 2 := Nat.pow_le_pow_left hS _
    _ ≤ #A * ∑ x ∈ A, (coverCount As x) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ N * (m * N + m * (m - 1) * b) := by
        rw [sum_coverCount_sq_eq_sum_inter_card h_sub]
        exact Nat.mul_le_mul_left N (sum_inter_card_le_of_subset h_sub h_pairwise)
    _ = m * N ^ 2 + m * (m - 1) * N * b := by ring

/-- **Corrádi's lemma, integer ratio form.**
Under `b · N ≤ a²` and `b ≤ a`, `m · (a² − b·N) ≤ N · (a − b)`. -/
theorem corradi_card_le (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, #(As i) = a)
    (h_pairwise : ∀ i j, i ≠ j → #(As i ∩ As j) ≤ b)
    (h_bN : b * #A ≤ a ^ 2) (h_ba : b ≤ a) :
    Fintype.card ι * (a ^ 2 - b * #A) ≤ #A * (a - b) := by
  set m := Fintype.card ι
  set N := #A
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have key := corradi_mul_le h_sub h_size h_pairwise (a := a) (b := b)
  have e1 : m ^ 2 * (a ^ 2 - b * N) + m ^ 2 * (b * N) = m ^ 2 * a ^ 2 := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h_bN]
  have e2 : m * N * (a - b) + m * N * b = m * N * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h_ba]
  have step : m ^ 2 * (a ^ 2 - b * N) ≤ m * N * (a - b) := by nlinarith [key, e1, e2]
  have : m * (m * (a ^ 2 - b * N)) ≤ m * (N * (a - b)) := by
    calc m * (m * (a ^ 2 - b * N))
        = m ^ 2 * (a ^ 2 - b * N) := by ring
      _ ≤ m * N * (a - b) := step
      _ = m * (N * (a - b)) := by ring
  exact Nat.le_of_mul_le_mul_left this hm

/-- **Corrádi's lemma, real-valued ratio form.**
The same ratio bound, stated in `ℝ` — no Nat-subtraction caveat on the
left-hand side. Still needs `b ≤ a` for the right-hand side. -/
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
