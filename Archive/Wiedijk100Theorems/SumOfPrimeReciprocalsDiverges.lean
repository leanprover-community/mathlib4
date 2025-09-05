/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Squarefree

/-!
# Divergence of the Prime Reciprocal Series

This file proves Theorem 81 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).
The theorem states that the sum of the reciprocals of all prime numbers diverges.
The formalization follows Erdős's proof by upper and lower estimates.

## Proof outline

1. Assume that the sum of the reciprocals of the primes converges.
2. Then there exists a `k : ℕ` such that, for any `x : ℕ`, the sum of the reciprocals of the primes
   between `k` and `x + 1` is less than 1/2 (`sum_lt_half_of_not_tendsto`).
3. For any `x : ℕ`, we can partition `range x` into two subsets (`range_sdiff_eq_biUnion`):
    * `M x k`, the subset of those `e` for which `e + 1` is a product of powers of primes smaller
      than or equal to `k`;
    * `U x k`, the subset of those `e` for which there is a prime `p > k` that divides `e + 1`.
4. Then `|U x k|` is bounded by the sum over the primes `p > k` of the number of multiples of `p`
   in `(k, x]`, which is at most `x / p`. It follows that `|U x k|` is at most `x` times the sum of
  the reciprocals of the primes between `k` and `x + 1`, which is less than 1/2 as noted in (2), so
  `|U x k| < x / 2` (`card_le_mul_sum`).
5. By factoring `e + 1 = (m + 1)² * (r + 1)`, `r + 1` squarefree and `m + 1 ≤ √x`, and noting that
   squarefree numbers correspond to subsets of `[1, k]`, we find that `|M x k| ≤ 2 ^ k * √x`
   (`card_le_two_pow_mul_sqrt`).
6. Finally, setting `x := (2 ^ (k + 1))²` (`√x = 2 ^ (k + 1)`), we find that
   `|M x k| ≤ 2 ^ k * 2 ^ (k + 1) = x / 2`. Combined with the strict bound for `|U k x|` from (4),
   `x = |M x k| + |U x k| < x / 2 + x / 2 = x`.

## References

https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes
-/

open Filter Finset

namespace Theorems100

/-- The primes in `(k, x]`.
-/
def P (x k : ℕ) : Finset ℕ := {p ∈ range (x + 1) | k < p ∧ p.Prime}

/-- The union over those primes `p ∈ (k, x]` of the sets of `e < x` for which `e + 1` is a multiple
of `p`, i.e., those `e < x` for which there is a prime `p ∈ (k, x]` that divides `e + 1`.
-/
def U (x k : ℕ) : Finset ℕ := (P x k).biUnion fun p ↦ {e ∈ range x | p ∣ e + 1}

open Classical in
/-- Those `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to `k`.
-/
noncomputable def M (x k : ℕ) : Finset ℕ := {e ∈ range x | ∀ p : ℕ, p.Prime ∧ p ∣ e + 1 → p ≤ k}

/--
If the sum of the reciprocals of the primes converges, there exists a `k : ℕ` such that the sum of
the reciprocals of the primes greater than `k` is less than 1/2.

More precisely, for any `x : ℕ`, the sum of the reciprocals of the primes between `k` and `x + 1`
is less than 1/2.
-/
theorem sum_lt_half_of_not_tendsto
    (h : ¬Tendsto (fun n => ∑ p ∈ range n with p.Prime, 1 / (p : ℝ))
      atTop atTop) :
    ∃ k, ∀ x, ∑ p ∈ P x k, 1 / (p : ℝ) < 1 / 2 := by
  have h0 :
    (fun n => ∑ p ∈ range n with p.Prime, 1 / (p : ℝ)) = fun n =>
      ∑ p ∈ range n, ite (Nat.Prime p) (1 / (p : ℝ)) 0 := by
    simp only [sum_filter]
  have hf : ∀ n : ℕ, 0 ≤ ite (Nat.Prime n) (1 / (n : ℝ)) 0 := by
    intro n; split_ifs
    · simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    · exact le_rfl
  rw [h0, ← summable_iff_not_tendsto_nat_atTop_of_nonneg hf, summable_iff_vanishing] at h
  obtain ⟨s, h⟩ := h (Set.Ioo (-1) (1 / 2)) (isOpen_Ioo.mem_nhds (by simp))
  obtain ⟨k, hk⟩ := exists_nat_subset_range s
  use k
  intro x
  rw [P, ← filter_filter, sum_filter]
  refine (h _ ?_).2
  rw [disjoint_iff_ne]
  simp only [mem_filter]
  intro a ha b hb
  exact ((mem_range.mp (hk hb)).trans ha.2).ne'

/--
Removing from {0, ..., x - 1} those elements `e` for which `e + 1` is a product of powers of primes
smaller than or equal to `k` leaves those `e` for which there is a prime `p > k` that divides
`e + 1`, or the union over those primes `p > k` of the sets of `e`s for which `e + 1` is a multiple
of `p`.
-/
theorem range_sdiff_eq_biUnion {x k : ℕ} : range x \ M x k = U x k := by
  ext e
  simp only [mem_biUnion, not_and, mem_sdiff, mem_filter, mem_range, U, M, P]
  push_neg
  constructor
  · rintro ⟨hex, hexh⟩
    obtain ⟨p, ⟨hpp, hpe1⟩, hpk⟩ := hexh hex
    refine ⟨p, ?_, ⟨hex, hpe1⟩⟩
    exact ⟨(Nat.le_of_dvd e.succ_pos hpe1).trans_lt (Nat.succ_lt_succ hex), hpk, hpp⟩
  · rintro ⟨p, hpfilter, ⟨hex, hpe1⟩⟩
    rw [imp_iff_right hex]
    exact ⟨hex, ⟨p, ⟨hpfilter.2.2, hpe1⟩, hpfilter.2.1⟩⟩

/--
The number of `e < x` for which `e + 1` has a prime factor `p > k` is bounded by `x` times the sum
of reciprocals of primes in `(k, x]`.
-/
theorem card_le_mul_sum {x k : ℕ} : #(U x k) ≤ x * ∑ p ∈ P x k, 1 / (p : ℝ) := by
  let P := {p ∈ range (x + 1) | k < p ∧ p.Prime}
  let N p := {e ∈ range x | p ∣ e + 1}
  have h : #(P.biUnion N) ≤ ∑ p ∈ P, #(N p) := card_biUnion_le
  calc
    (#(P.biUnion N) : ℝ) ≤ ∑ p ∈ P, (#(N p) : ℝ) := by assumption_mod_cast
    _ ≤ ∑ p ∈ P, x * (1 / (p : ℝ)) := sum_le_sum fun p _ => ?_
    _ = x * ∑ p ∈ P, 1 / (p : ℝ) := by rw [mul_sum]
  simp only [N, mul_one_div, Nat.card_multiples, Nat.cast_div_le]

/--
The number of `e < x` for which `e + 1` is a squarefree product of primes smaller than or equal to
`k` is bounded by `2 ^ k`, the number of subsets of `[1, k]`.
-/
theorem card_le_two_pow {x k : ℕ} : #{e ∈ M x k | Squarefree (e + 1)} ≤ 2 ^ k := by
  let M₁ := {e ∈ M x k | Squarefree (e + 1)}
  let f s := (∏ a ∈ s, a) - 1
  let K := powerset (image Nat.succ (range k))
  -- Take `e` in `M x k`. If `e + 1` is squarefree, then it is the product of a subset of `[1, k]`.
  -- It follows that `e` is one less than such a product.
  have h : M₁ ⊆ image f K := by
    intro m hm
    simp only [f, K, M₁, M, mem_filter, mem_range, mem_powerset, mem_image] at hm ⊢
    obtain ⟨⟨-, hmp⟩, hms⟩ := hm
    use! (m + 1).primeFactorsList
    · rwa [Multiset.coe_nodup, ← Nat.squarefree_iff_nodup_primeFactorsList m.succ_ne_zero]
    refine ⟨fun p => ?_, ?_⟩
    · suffices p ∈ (m + 1).primeFactorsList → ∃ a : ℕ, a < k ∧ a.succ = p by simpa
      simp only [Nat.mem_primeFactorsList m.succ_ne_zero]
      intro hp
      exact
        ⟨p.pred, (Nat.pred_lt (Nat.Prime.ne_zero hp.1)).trans_le ((hmp p) hp),
          Nat.succ_pred_eq_of_pos (Nat.Prime.pos hp.1)⟩
    · simp [Nat.prod_primeFactorsList m.succ_ne_zero, m.add_one_sub_one]
  -- The number of elements of `M x k` with `e + 1` squarefree is bounded by the number of subsets
  -- of `[1, k]`.
  calc
    #M₁ ≤ #(image f K) := card_le_card h
    _ ≤ #K := card_image_le
    _ ≤ 2 ^ #(image Nat.succ (range k)) := by simp only [K, card_powerset]; rfl
    _ ≤ 2 ^ #(range k) := pow_right_mono₀ one_le_two card_image_le
    _ = 2 ^ k := by rw [card_range k]

/--
The number of `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to
`k` is bounded by `2 ^ k * nat.sqrt x`.
-/
theorem card_le_two_pow_mul_sqrt {x k : ℕ} : #(M x k) ≤ 2 ^ k * Nat.sqrt x := by
  let M₁ := {e ∈ M x k | Squarefree (e + 1)}
  let M₂ := M (Nat.sqrt x) k
  let K := M₁ ×ˢ M₂
  let f : ℕ × ℕ → ℕ := fun mn => (mn.2 + 1) ^ 2 * (mn.1 + 1) - 1
  -- Every element of `M x k` is one less than the product `(m + 1)² * (r + 1)` with `r + 1`
  -- squarefree and `m + 1 ≤ √x`, and both `m + 1` and `r + 1` still only have prime powers
  -- smaller than or equal to `k`.
  have h1 : M x k ⊆ image f K := by
    intro m hm
    simp only [f, K, M, M₁, M₂, mem_image, Prod.exists, mem_product,
               mem_filter, mem_range] at hm ⊢
    have hm' := m.zero_lt_succ
    obtain ⟨a, b, hab₁, hab₂⟩ := Nat.sq_mul_squarefree_of_pos' hm'
    obtain ⟨ham, hbm⟩ := Dvd.intro_left _ hab₁, Dvd.intro _ hab₁
    refine ⟨a, b, ⟨⟨⟨?_, fun p hp => ?_⟩, hab₂⟩, ⟨?_, fun p hp => ?_⟩⟩, by
        simp_rw [hab₁, m.add_one_sub_one]⟩
    · exact (Nat.succ_le_succ_iff.mp (Nat.le_of_dvd hm' ham)).trans_lt hm.1
    · exact hm.2 p ⟨hp.1, hp.2.trans ham⟩
    · calc
        b < b + 1 := lt_add_one b
        _ ≤ (m + 1).sqrt := by simpa only [Nat.le_sqrt, pow_two] using Nat.le_of_dvd hm' hbm
        _ ≤ x.sqrt := Nat.sqrt_le_sqrt (Nat.succ_le_iff.mpr hm.1)
    · exact hm.2 p ⟨hp.1, hp.2.trans (Nat.dvd_of_pow_dvd one_le_two hbm)⟩
  have h2 : #M₂ ≤ Nat.sqrt x := by
    rw [← card_range (Nat.sqrt x)]; apply card_le_card; simp [M, M₂]
  calc
    #(M x k) ≤ #(image f K) := card_le_card h1
    _ ≤ #K := card_image_le
    _ = #M₁ * #M₂ := card_product M₁ M₂
    _ ≤ 2 ^ k * x.sqrt := mul_le_mul' card_le_two_pow h2

theorem Real.tendsto_sum_one_div_prime_atTop :
    Tendsto (fun n => ∑ p ∈ range n with p.Prime, 1 / (p : ℝ))
      atTop atTop := by
  -- Assume that the sum of the reciprocals of the primes converges.
  by_contra h
  -- Then there is a natural number `k` such that for all `x`, the sum of the reciprocals of primes
  -- between `k` and `x` is less than 1/2.
  obtain ⟨k, h1⟩ := sum_lt_half_of_not_tendsto h
  -- Choose `x` sufficiently large for the argument below to work, and use a perfect square so we
  -- can easily take the square root.
  let x := 2 ^ (k + 1) * 2 ^ (k + 1)
  -- We will partition `range x` into two subsets:
  -- * `M`, the subset of those `e` for which `e + 1` is a product of powers of primes smaller
  --   than or equal to `k`;
  set M' := M x k with hM'
  -- * `U`, the subset of those `e` for which there is a prime `p > k` that divides `e + 1`.
  let P := {p ∈ range (x + 1) | k < p ∧ p.Prime}
  set U' := U x k with hU'
  -- This is indeed a partition, so `|U| + |M| = |range x| = x`.
  have h2 : x = #U' + #M' := by
    rw [← card_range x, hU', hM', ← range_sdiff_eq_biUnion]
    classical
    exact (card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).symm
  -- But for the `x` we have chosen above, both `|U|` and `|M|` are less than or equal to `x / 2`,
  -- and for U, the inequality is strict.
  have h3 :=
    calc
      (#U' : ℝ) ≤ x * ∑ p ∈ P, 1 / (p : ℝ) := card_le_mul_sum
      _ < x * (1 / 2) := mul_lt_mul_of_pos_left (h1 x) (by simp [x])
      _ = x / 2 := mul_one_div (x : ℝ) 2
  have h4 :=
    calc
      (#M' : ℝ) ≤ 2 ^ k * x.sqrt := by exact mod_cast card_le_two_pow_mul_sqrt
      _ = 2 ^ k * (2 ^ (k + 1) : ℕ) := by rw [Nat.sqrt_eq]
      _ = x / 2 := by simp [field, x, ← pow_succ]
  refine lt_irrefl (x : ℝ) ?_
  calc
    (x : ℝ) = (#U' : ℝ) + (#M' : ℝ) := by assumption_mod_cast
    _ < x / 2 + x / 2 := add_lt_add_of_lt_of_le h3 h4
    _ = x := add_halves (x : ℝ)

end Theorems100
