/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.GroupTheory.Perm.Fin

/-!
# IMO 2001 Q4

Let $n > 1$ be an odd integer and let $c_1, c_2, \dots, c_n$ be integers. For each permutation
$a = (a_1, a_2, \dots, a_n)$ of $\{1, 2, \dots, n\}$, define $S(a) = \sum_{i=1}^n c_i a_i$.
Prove that there exist two permutations $a ≠ b$ of $\{1, 2, \dots, n\}$ such that
$n!$ is a divisor of $S(a) - S(b)$.

# Solution

Suppose for contradiction that all the $S(a)$ have distinct residues modulo $n!$, then
$$\sum_{i=0}^{n!-1} i ≡ \sum_a S(a) = \sum_i c_i \sum_a a_i = (n-1)! \frac{n(n+1)}2 \sum_i c_i$$
$$= n! \frac{n+1}2 \sum_i c_i ≡ 0 \bmod n$$
where the last equality relies on $n$ being odd. But $\sum_{i=0}^{n!-1} i = \frac{n!(n!-1)}2$
is not divisible by $n!$, since the quotient is $\frac{n!-1}2$ and $n!$ is even when $n > 1$.
-/

namespace Imo2001Q4

open Equiv Finset
open scoped Nat

variable {n : ℕ} {c : Fin n → ℤ}

/-- The function `S` in the problem. As implemented here it accepts a permutation of `Fin n`
rather than `Icc 1 n`, and as such contains `+ 1` to compensate. -/
def S (c : Fin n → ℤ) (a : Perm (Fin n)) : ℤ := ∑ i, c i * (a i + 1)

/-- Assuming the opposite of what is to be proved, the sum of `S` over all permutations is
congruent to the sum of all residues modulo `n!`, i.e. `n! * (n! - 1) / 2`. -/
lemma sum_range_modEq_sum_of_contra (hS : ¬∃ a b, a ≠ b ∧ (n ! : ℤ) ∣ S c a - S c b) :
    n ! * ((n ! : ℤ) - 1) / 2 ≡ ∑ a, S c a [ZMOD n !] := by
  have mir : ∀ a, S c a % n ! ∈ Ico (0 : ℤ) n ! := fun a ↦ by
    rw [mem_Ico]; constructor
    · exact Int.emod_nonneg _ (by positivity)
    · exact Int.emod_lt_of_pos _ (by positivity)
  let f : Perm (Fin n) → Ico (0 : ℤ) n ! := fun a ↦ ⟨_, mir a⟩
  have bijf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card, Fintype.card_coe, Int.card_Ico, sub_zero,
      Int.toNat_natCast, Fintype.card_perm, Fintype.card_fin]; refine ⟨?_, rfl⟩
    contrapose! hS; unfold Function.Injective at hS; push_neg at hS; obtain ⟨a, b, he, hn⟩ := hS
    use a, b, hn; simp only [f, Subtype.mk.injEq] at he; exact Int.ModEq.dvd he.symm
  let e : Perm (Fin n) ≃ Ico (0 : ℤ) n ! := ofBijective _ bijf
  change _ % _ = _ % _; rw [sum_int_mod]; congr 1
  change _ = ∑ i, (e i).1; rw [Equiv.sum_comp]
  change _ = ∑ i : { x // x ∈ _ }, id i.1; simp_rw [sum_coe_sort, id_eq]
  have Ico_eq : Ico (0 : ℤ) n ! = (range n !).map ⟨_, Nat.cast_injective⟩ := by
    ext i
    simp_rw [mem_Ico, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor <;> intro h
    · lift i to ℕ using h.1; rw [Nat.cast_lt] at h; simp [h.2]
    · obtain ⟨z, lz, rfl⟩ := h; simp [lz]
  rw [Ico_eq, sum_map, Function.Embedding.coeFn_mk, ← Nat.cast_sum, sum_range_id]
  change _ = ((_ : ℕ) : ℤ) / (2 : ℕ)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pred (Nat.factorial_pos n)]

/-- The sum over all permutations of `Icc 1 n` of the entry at any fixed position is
`(n - 1)! * (n * (n + 1) / 2)`. -/
lemma sum_perm_add_one {i : Fin n} (hn : 1 ≤ n) :
    ∑ a : Perm (Fin n), ((a i).1 + 1) = (n - 1)! * (n * (n + 1) / 2) := by
  rw [le_iff_exists_add'] at hn; obtain ⟨n, rfl⟩ := hn
  rw [← sum_comp (Equiv.mulRight (swap i 0))]
  simp_rw [coe_mulRight, Perm.coe_mul, Function.comp_apply, swap_apply_left, univ_perm_fin_succ,
    sum_map, coe_toEmbedding, Fintype.sum_prod_type, Perm.decomposeFin_symm_apply_zero, sum_const,
    smul_eq_mul, ← mul_sum, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  congr
  have es := sum_range_add id 1 (n + 1)
  simp_rw [id_eq, sum_range_one, zero_add, add_comm 1] at es
  rw [Fin.sum_univ_eq_sum_range (· + 1), ← es, sum_range_id, add_tsub_cancel_right, mul_comm]

/-- For odd `n`, the sum of `S` over all permutations is divisible by `n!`. -/
lemma sum_modEq_zero_of_odd (hn : Odd n) : ∑ a, S c a ≡ 0 [ZMOD n !] := by
  unfold S; rw [sum_comm]
  conv_lhs => enter [2, i, 2, a]; rw [← Nat.cast_one, ← Nat.cast_add]
  simp_rw [← mul_sum, ← Nat.cast_sum]
  have eqv : ∀ i, c i * ↑(∑ a : Perm (Fin n), ((a i).1 + 1)) =
      c i * ((n - 1)! * (n * (n + 1) / 2) : ℕ) := fun i ↦ by rw [sum_perm_add_one hn.pos]
  rw [sum_congr rfl fun i _ ↦ eqv i, ← sum_mul,
    Nat.mul_div_assoc _ (hn.add_odd odd_one).two_dvd, ← mul_assoc, mul_comm _ n,
    Nat.mul_factorial_pred hn.pos.ne', Nat.cast_mul, ← mul_assoc, ← mul_rotate]
  exact (Int.dvd_mul_left ..).modEq_zero_int

theorem result (hn : Odd n ∧ 1 < n) : ∃ a b, a ≠ b ∧ (n ! : ℤ) ∣ S c a - S c b := by
  by_contra h
  have key := (sum_range_modEq_sum_of_contra h).trans (sum_modEq_zero_of_odd hn.1)
  rw [Int.modEq_zero_iff_dvd, dvd_def] at key; obtain ⟨c, hc⟩ := key
  have feven : 2 ∣ (n ! : ℤ) := mod_cast Nat.dvd_factorial zero_lt_two hn.2
  nth_rw 3 [← Int.ediv_mul_cancel feven] at hc
  rw [mul_comm, Int.mul_ediv_assoc _ feven, mul_rotate] at hc
  have halfpos : 0 < (n ! : ℤ) / 2 :=
    Int.ediv_pos_of_pos_of_dvd (by positivity) zero_le_two feven
  rw [mul_left_inj' halfpos.ne', sub_eq_iff_eq_add] at hc
  rw [← even_iff_two_dvd, ← Int.not_odd_iff_even] at feven
  exact feven ⟨_, hc⟩

end Imo2001Q4
