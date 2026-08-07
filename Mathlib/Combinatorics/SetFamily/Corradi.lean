/-
Copyright (c) 2026 Andrew Zitek-Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada, Ziyi Guan, Ignacio Manzur
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!

S. Jukna, *Extremal Combinatorics* (Springer, 2011)
Lemma 2.1 (Corrádi 1969).

Let A₁, A₂, ..., Aₙ be r-element sets and X be their union. If |Aᵢ ∩ Aⱼ| ≤ k
for all i ≠ j, then
  |X| ≥ r²n / (r + (n - 1)k)

Since Finset.card values are ℕ truncations can occur.
The core inequality must be stated without division, subtraction:
* `Finset.corradi_mul_le`
  n²r² + n|X|k ≤ n|X|r + n²|X|k

Casting to ℝ recovers the readable ratio form:
* `Finset.corradi_card_le_real`
  n·(r² − k·|X|) ≤ |X|·(r − k)

-/

@[expose] public section

namespace Finset

-- alpha is set member type. any type where you can compute if two elements are equal
variable {α : Type*} [DecidableEq α]

-- iota is index of set family. any finite type (you can get cardinality) and decidable
variable {ι : Type*} [Fintype ι]

-- A is the set family
variable {A : ι → Finset α}

-- n is the size of the family. (matching Jukna notation)
local notation "n" => Fintype.card ι

-- X will be used as the union of all sets in the family
variable {X : Finset α}

-- r is how many elements in each set of the family and k is the intersection bound
variable {r k : ℕ}

-- number of sets in the family containing x (the degree of x).
  --   ι side  ("above")   i₁   i₂   i₃
  --                       /    /
  --   α side  ("below")    x
private abbrev degree (x : α) : ℕ := #(univ.bipartiteAbove (fun x i => x ∈ A i) x)
private abbrev sq_degree (x : α) : ℕ := (degree (A := A) x) ^ 2

-- sq_degree equals number of ordered pairs (i, j) with x ∈ Aᵢ and x ∈ Aⱼ
private lemma sq_degree_eq (x : α) : sq_degree (A := A) x =
    #(univ.bipartiteAbove (fun x (i, j) => x ∈ A i ∧ x ∈ A j) x) := by
  simp only [sq_degree, degree, bipartiteAbove, sq, ← card_product]
  -- congr 1 strips #(...)
  -- ext <i, j> show two finsets are equal via membership by each element
  congr 1; ext ⟨i, j⟩; simp

/-- sum of degrees squared is same as sum of pairwise intersection
    ∑{x ∈ X} dx² = ∑{i, j} |Aᵢ ∩ Aⱼ| -/
private lemma sum_sq_degree_eq
  (h_sub : ∀ i, A i ⊆ X) :
    ∑ x ∈ X, (sq_degree (A := A) x) = ∑ i : ι, ∑ j : ι, #(A i ∩ A j) := by
  classical
  rw [← sum_product', univ_product_univ]
  simp_rw [sq_degree_eq (A := A), sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  refine sum_congr rfl fun p _ => congr_arg _ ?_
  ext x; simp only [bipartiteBelow, mem_filter, mem_inter]
  exact ⟨fun ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h_sub _ h₁, h₁, h₂⟩⟩

/-- the pairwise intersection (rhs above)
    ∑{i, j} |Aᵢ ∩ Aⱼ| ≤ n⋆r + n⋆(n-1)⋆k -/
private lemma sum_inter_card_le
  (h_size : ∀ i, #(A i) = r)
  (h_pairwise : Pairwise fun i j => #(A i ∩ A j) ≤ k) :
    ∑ i : ι, ∑ j : ι, #(A i ∩ A j) ≤ n * r + n * (n - 1) * k := by
  classical
  have h_inner : ∀ i : ι, ∑ j, #(A i ∩ A j) ≤ r + (n - 1) * k := by
    intro i
    rw [← add_sum_erase _ _ (mem_univ i), inter_self, h_size]
    refine Nat.add_le_add_left ?_ r
    calc ∑ j ∈ univ.erase i, #(A i ∩ A j)
        ≤ ∑ _j ∈ univ.erase i, k :=
          sum_le_sum fun j hj => h_pairwise (ne_of_mem_erase hj).symm
      _ = (n - 1) * k := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, smul_eq_mul]
  calc ∑ i, ∑ j, #(A i ∩ A j)
      ≤ ∑ _i : ι, (r + (n - 1) * k) := sum_le_sum fun i _ => h_inner i
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_add, ← mul_assoc]

/-- `Finset.corradi_mul_le`
    n²r² + n|X|k ≤ n|X|r + n²|X|k -/
theorem corradi_mul_le
  (h_sub : ∀ i, A i ⊆ X)
  (h_size : ∀ i, #(A i) = r)
  (h_pairwise : Pairwise fun i j => #(A i ∩ A j) ≤ k) :
    n ^ 2 * r ^ 2 + n * #X * k ≤ n * #X * r + n ^ 2 * #X * k := by
  have hCS : (n * r) ^ 2 ≤ #X * (n * r + n * (n - 1) * k) :=
    calc (n * r) ^ 2
        = (∑ x ∈ X, #(univ.bipartiteAbove (· ∈ A ·) x)) ^ 2 := by
          rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow,
    sum_congr rfl fun i _ => by
      rw [bipartiteBelow, filter_mem_eq_inter, inter_eq_right.mpr (h_sub i)],
    sum_congr rfl (fun i _ => h_size i), sum_const, card_univ, smul_eq_mul]
      _ ≤ #X * ∑ x ∈ X, (degree (A := A) x) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ #X * (n * r + n * (n - 1) * k) := by
          rw [sum_sq_degree_eq h_sub]
          exact Nat.mul_le_mul_left _ (sum_inter_card_le h_size h_pairwise)
  rcases Nat.eq_zero_or_pos n with hm | hm
  · simp [hm]
  obtain ⟨m, hm'⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [hm'] at hCS ⊢
  simp only [Nat.add_sub_cancel] at hCS
  nlinarith [hCS, sq_nonneg m, Nat.zero_le r, Nat.zero_le k, Nat.zero_le (#X)]

/-- `Finset.corradi_card_le_real`
    n·(r² − k·|X|) ≤ |X|·(r − k) -/
theorem corradi_card_le_real (h_sub : ∀ i, A i ⊆ X)
  (h_size : ∀ i, #(A i) = r)
  (h_pairwise : Pairwise fun i j => #(A i ∩ A j) ≤ k)
  (h_ba : k ≤ r) :
    n * (r ^ 2 - k * #X) ≤ (#X : ℝ) * (r - k) := by
  have key_real : (n : ℝ) ^ 2 * (r : ℝ) ^ 2 + (n : ℝ) * #X * k ≤
      (n : ℝ) * #X * r + (n : ℝ) ^ 2 * #X * k := by
    exact_mod_cast corradi_mul_le h_sub h_size h_pairwise (r := r) (k := k)
  rcases Nat.eq_zero_or_pos n with hm | hm
  · simp only [hm, Nat.cast_zero, zero_mul]
    have : (0 : ℝ) ≤ (r : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast h_ba)
    positivity
  · have hmR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    nlinarith [key_real, hmR, sq_nonneg ((n : ℝ) - 1)]

end Finset
