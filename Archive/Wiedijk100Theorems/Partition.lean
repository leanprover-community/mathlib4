/-
Copyright (c) 2020 Bhavik Mehta, Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Aaron Anderson
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Partition
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ApplyFun

#align_import wiedijk_100_theorems.partition from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# Euler's Partition Theorem

This file proves Theorem 45 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem concerns the counting of integer partitions -- ways of
writing a positive integer `n` as a sum of positive integer parts.

Specifically, Euler proved that the number of integer partitions of `n`
into *distinct* parts equals the number of partitions of `n` into *odd*
parts.

## Proof outline

The proof is based on the generating functions for odd and distinct partitions, which turn out to be
equal:

$$\prod_{i=0}^\infty \frac {1}{1-X^{2i+1}} = \prod_{i=0}^\infty (1+X^{i+1})$$

In fact, we do not take a limit: it turns out that comparing the `n`'th coefficients of the partial
products up to `m := n + 1` is sufficient.

In particular, we

1. define the partial product for the generating function for odd partitions `partialOddGF m` :=
  $$\prod_{i=0}^m \frac {1}{1-X^{2i+1}}$$;
2. prove `oddGF_prop`: if `m` is big enough (`m * 2 > n`), the partial product's coefficient counts
  the number of odd partitions;
3. define the partial product for the generating function for distinct partitions
  `partialDistinctGF m` := $$\prod_{i=0}^m (1+X^{i+1})$$;
4. prove `distinctGF_prop`: if `m` is big enough (`m + 1 > n`), the `n`th coefficient of the
  partial product counts the number of distinct partitions of `n`;
5. prove `same_coeffs`: if m is big enough (`m ≥ n`), the `n`th coefficient of the partial products
  are equal;
6. combine the above in `partition_theorem`.

## References
https://en.wikipedia.org/wiki/Partition_(number_theory)#Odd_parts_and_distinct_parts
-/


open PowerSeries

namespace Theorems100

noncomputable section

variable {α : Type*}

open Finset

open scoped BigOperators

open scoped Classical

/-- The partial product for the generating function for odd partitions.
TODO: As `m` tends to infinity, this converges (in the `X`-adic topology).

If `m` is sufficiently large, the `i`th coefficient gives the number of odd partitions of the
natural number `i`: proved in `oddGF_prop`.
It is stated for an arbitrary field `α`, though it usually suffices to use `ℚ` or `ℝ`.
-/
def partialOddGF (m : ℕ) [Field α] :=
  ∏ i in range m, (1 - (X : PowerSeries α) ^ (2 * i + 1))⁻¹
#align theorems_100.partial_odd_gf Theorems100.partialOddGF

/-- The partial product for the generating function for distinct partitions.
TODO: As `m` tends to infinity, this converges (in the `X`-adic topology).

If `m` is sufficiently large, the `i`th coefficient gives the number of distinct partitions of the
natural number `i`: proved in `distinctGF_prop`.
It is stated for an arbitrary commutative semiring `α`, though it usually suffices to use `ℕ`, `ℚ`
or `ℝ`.
-/
def partialDistinctGF (m : ℕ) [CommSemiring α] :=
  ∏ i in range m, (1 + (X : PowerSeries α) ^ (i + 1))
#align theorems_100.partial_distinct_gf Theorems100.partialDistinctGF

/--
Functions defined only on `s`, which sum to `n`. In other words, a partition of `n` indexed by `s`.
Every function in here is finitely supported, and the support is a subset of `s`.
This should be thought of as a generalisation of `Finset.Nat.antidiagonalTuple` where
`antidiagonalTuple k n` is the same thing as `cut (s : Finset.univ (Fin k)) n`.
-/
def cut {ι : Type*} (s : Finset ι) (n : ℕ) : Finset (ι → ℕ) :=
  Finset.filter (fun f => s.sum f = n)
    ((s.pi fun _ => range (n + 1)).map
      ⟨fun f i => if h : i ∈ s then f i h else 0, fun f g h => by
        ext i hi; simpa [dif_pos hi] using congr_fun h i⟩)
#align theorems_100.cut Theorems100.cut

theorem mem_cut {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    f ∈ cut s n ↔ s.sum f = n ∧ ∀ i, i ∉ s → f i = 0 := by
  rw [cut, mem_filter, and_comm, and_congr_right]
  intro h
  simp only [mem_map, exists_prop, Function.Embedding.coeFn_mk, mem_pi]
  constructor
  · rintro ⟨_, _, rfl⟩ _ H
    simp [dif_neg H]
  · intro hf
    refine' ⟨fun i _ => f i, fun i hi => _, _⟩
    · rw [mem_range, Nat.lt_succ_iff, ← h]
      apply single_le_sum _ hi
      simp
    · ext x
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm]
      exact hf x
#align theorems_100.mem_cut Theorems100.mem_cut

theorem cut_equiv_antidiag (n : ℕ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (cut univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk, ←
    Equiv.eq_symm_apply]
  simp [mem_cut, add_comm]
#align theorems_100.cut_equiv_antidiag Theorems100.cut_equiv_antidiag

theorem cut_univ_fin_eq_antidiagonalTuple (n : ℕ) (k : ℕ) :
    cut univ n = Nat.antidiagonalTuple k n := by ext; simp [Nat.mem_antidiagonalTuple, mem_cut]
#align theorems_100.cut_univ_fin_eq_antidiagonal_tuple Theorems100.cut_univ_fin_eq_antidiagonalTuple

/-- There is only one `cut` of 0. -/
@[simp]
theorem cut_zero {ι : Type*} (s : Finset ι) : cut s 0 = {0} := by
  -- In general it's nice to prove things using `mem_cut` but in this case it's easier to just
  -- use the definition.
  rw [cut, range_one, pi_const_singleton, map_singleton, Function.Embedding.coeFn_mk,
    filter_singleton, if_pos, singleton_inj]
  · ext; split_ifs <;> rfl
  rw [sum_eq_zero_iff]
  intro x hx
  apply dif_pos hx
#align theorems_100.cut_zero Theorems100.cut_zero

@[simp]
theorem cut_empty_succ {ι : Type*} (n : ℕ) : cut (∅ : Finset ι) (n + 1) = ∅ := by
  apply eq_empty_of_forall_not_mem
  intro x hx
  rw [mem_cut, sum_empty] at hx
  cases hx.1
#align theorems_100.cut_empty_succ Theorems100.cut_empty_succ

theorem cut_insert {ι : Type*} (n : ℕ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    cut (insert a s) n =
      (antidiagonal n).biUnion fun p : ℕ × ℕ =>
        (cut s p.snd).map
          ⟨fun f => f + fun t => if t = a then p.fst else 0, add_left_injective _⟩ := by
  ext f
  rw [mem_cut, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, mem_antidiagonal, Prod.exists]
    refine' ⟨f a, s.sum f, rfl, fun i => if i = a then 0 else f i, _, _⟩
    · rw [mem_cut]
      refine' ⟨_, _⟩
      · rw [sum_ite]
        have : filter (fun x => x ≠ a) s = s := by
          apply filter_true_of_mem
          rintro i hi rfl
          apply h hi
        simp [this]
      · intro i hi
        rw [ite_eq_left_iff]
        intro hne
        apply h₁
        simp [not_or, hne, hi]
    · ext x
      obtain rfl | h := eq_or_ne x a
      · simp
      · simp [if_neg h]
  · simp only [mem_insert, Function.Embedding.coeFn_mk, mem_map, mem_antidiagonal, Prod.exists,
      exists_prop, mem_cut, not_or]
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩
    refine' ⟨_, _⟩
    · simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm]
    · rintro i ⟨h₁, h₂⟩
      simp [if_neg h₁, hg₂ _ h₂]
#align theorems_100.cut_insert Theorems100.cut_insert

theorem coeff_prod_range [CommSemiring α] {ι : Type*} (s : Finset ι) (f : ι → PowerSeries α)
    (n : ℕ) : coeff α n (∏ j in s, f j) = ∑ l in cut s n, ∏ i in s, coeff α (l i) (f i) := by
  revert n
  induction s using Finset.induction_on with
  | empty =>
    rintro ⟨_ | n⟩
    · simp
    simp [cut_empty_succ, if_neg (Nat.succ_ne_zero _)]
  | @insert a s hi ih =>
    intro n
    rw [cut_insert _ _ _ hi, prod_insert hi, coeff_mul, sum_biUnion]
    · congr with i
      simp only [sum_map, Pi.add_apply, Function.Embedding.coeFn_mk, prod_insert hi, if_pos rfl, ih,
        mul_sum]
      apply sum_congr rfl _
      intro x hx
      rw [mem_cut] at hx
      rw [hx.2 a hi, zero_add]
      congr 1
      apply prod_congr rfl
      intro k hk
      rw [if_neg, add_zero]
      exact ne_of_mem_of_not_mem hk hi
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, Prod.forall, not_and, Ne.def,
        mem_antidiagonal, disjoint_left, mem_map, exists_prop, Function.Embedding.coeFn_mk,
        exists_imp, not_exists, Finset.mem_coe, Function.onFun, mem_cut, and_imp]
      rintro p₁ q₁ rfl p₂ q₂ h t x p hp _ hp3 q hq _ hq3
      have z := hp3.trans hq3.symm
      have := sum_congr (Eq.refl s) fun x _ => Function.funext_iff.1 z x
      obtain rfl : q₁ = q₂ := by simpa [sum_add_distrib, hp, hq, if_neg hi] using this
      obtain rfl : p₂ = p₁ := by simpa using h
      exact (t rfl).elim
#align theorems_100.coeff_prod_range Theorems100.coeff_prod_range

/-- A convenience constructor for the power series whose coefficients indicate a subset. -/
def indicatorSeries (α : Type*) [Semiring α] (s : Set ℕ) : PowerSeries α :=
  PowerSeries.mk fun n => if n ∈ s then 1 else 0
#align theorems_100.indicator_series Theorems100.indicatorSeries

theorem coeff_indicator (s : Set ℕ) [Semiring α] (n : ℕ) :
    coeff α n (indicatorSeries _ s) = if n ∈ s then 1 else 0 :=
  coeff_mk _ _
#align theorems_100.coeff_indicator Theorems100.coeff_indicator

theorem coeff_indicator_pos (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∈ s) :
    coeff α n (indicatorSeries _ s) = 1 := by rw [coeff_indicator, if_pos h]
#align theorems_100.coeff_indicator_pos Theorems100.coeff_indicator_pos

theorem coeff_indicator_neg (s : Set ℕ) [Semiring α] (n : ℕ) (h : n ∉ s) :
    coeff α n (indicatorSeries _ s) = 0 := by rw [coeff_indicator, if_neg h]
#align theorems_100.coeff_indicator_neg Theorems100.coeff_indicator_neg

theorem constantCoeff_indicator (s : Set ℕ) [Semiring α] :
    constantCoeff α (indicatorSeries _ s) = if 0 ∈ s then 1 else 0 :=
  rfl
#align theorems_100.constant_coeff_indicator Theorems100.constantCoeff_indicator

theorem two_series (i : ℕ) [Semiring α] :
    1 + (X : PowerSeries α) ^ i.succ = indicatorSeries α {0, i.succ} := by
  ext n
  simp only [coeff_indicator, coeff_one, coeff_X_pow, Set.mem_insert_iff, Set.mem_singleton_iff,
    map_add]
  cases' n with d
  · simp [(Nat.succ_ne_zero i).symm]
  · simp [Nat.succ_ne_zero d]
#align theorems_100.two_series Theorems100.two_series

theorem num_series' [Field α] (i : ℕ) :
    (1 - (X : PowerSeries α) ^ (i + 1))⁻¹ = indicatorSeries α {k | i + 1 ∣ k} := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · ext n
    cases n with
    | zero => simp [mul_sub, zero_pow, constantCoeff_indicator]
    | succ n =>
      simp only [coeff_one, if_false, mul_sub, mul_one, coeff_indicator,
        LinearMap.map_sub]
      simp_rw [coeff_mul, coeff_X_pow, coeff_indicator, @boole_mul _ _ _ _]
      erw [sum_ite, sum_ite]
      simp_rw [@filter_filter _ _ _ _ _, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one,
        sub_eq_iff_eq_add, zero_add]
      symm
      split_ifs with h
      · suffices
          ((antidiagonal n.succ).filter fun a : ℕ × ℕ => i + 1 ∣ a.fst ∧ a.snd = i + 1).card =
            1 by
          simp only [Set.mem_setOf_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
        rw [card_eq_one]
        cases' h with p hp
        refine' ⟨((i + 1) * (p - 1), i + 1), _⟩
        ext ⟨a₁, a₂⟩
        simp only [mem_filter, Prod.mk.inj_iff, mem_antidiagonal, mem_singleton]
        constructor
        · rintro ⟨a_left, ⟨a, rfl⟩, rfl⟩
          refine' ⟨_, rfl⟩
          rw [Nat.mul_sub_left_distrib, ← hp, ← a_left, mul_one, Nat.add_sub_cancel]
        · rintro ⟨rfl, rfl⟩
          match p with
          | 0 => rw [mul_zero] at hp; cases hp
          | p + 1 => rw [hp]; simp [mul_add]
      · suffices
          (filter (fun a : ℕ × ℕ => i + 1 ∣ a.fst ∧ a.snd = i + 1) (antidiagonal n.succ)).card =
            0 by
          simp only [Set.mem_setOf_eq]; convert congr_arg ((↑) : ℕ → α) this; norm_cast
        rw [card_eq_zero]
        apply eq_empty_of_forall_not_mem
        simp only [Prod.forall, mem_filter, not_and, mem_antidiagonal]
        rintro _ h₁ h₂ ⟨a, rfl⟩ rfl
        apply h
        simp [← h₂]
  · simp [zero_pow]
#align theorems_100.num_series' Theorems100.num_series'

def mkOdd : ℕ ↪ ℕ :=
  ⟨fun i => 2 * i + 1, fun x y h => by linarith⟩
#align theorems_100.mk_odd Theorems100.mkOdd

-- The main workhorse of the partition theorem proof.
theorem partialGF_prop (α : Type*) [CommSemiring α] (n : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i)
    (c : ℕ → Set ℕ) (hc : ∀ i, i ∉ s → 0 ∈ c i) :
    (Finset.card
          ((univ : Finset (Nat.Partition n)).filter fun p =>
            (∀ j, p.parts.count j ∈ c j) ∧ ∀ j ∈ p.parts, j ∈ s) :
        α) =
      (coeff α n) (∏ i : ℕ in s, indicatorSeries α ((· * i) '' c i)) := by
  simp_rw [coeff_prod_range, coeff_indicator, prod_boole, sum_boole]
  congr 1
  refine' Finset.card_congr (fun p _ i => Multiset.count i p.parts • i) _ _ _
  · simp only [mem_filter, mem_cut, mem_univ, true_and_iff, exists_prop, and_assoc, and_imp,
      smul_eq_zero, Function.Embedding.coeFn_mk, exists_imp]
    rintro ⟨p, hp₁, hp₂⟩ hp₃ hp₄
    dsimp only at *
    refine' ⟨_, _, _⟩
    · rw [← hp₂, ←
        sum_multiset_count_of_subset p s fun x hx => hp₄ _ (Multiset.mem_toFinset.mp hx)]
    · intro i hi
      left
      exact Multiset.count_eq_zero_of_not_mem (mt (hp₄ i) hi)
    · exact fun i _ => ⟨_, hp₃ i, rfl⟩
  · dsimp only
    intro p₁ p₂ hp₁ hp₂ h
    apply Nat.Partition.ext
    simp only [true_and_iff, mem_univ, mem_filter] at hp₁ hp₂
    ext i
    rw [Function.funext_iff] at h
    specialize h i
    match i with
    | 0 =>
      rw [Multiset.count_eq_zero_of_not_mem]
      rw [Multiset.count_eq_zero_of_not_mem]
      intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₂.2 0 a))
      intro a; exact Nat.lt_irrefl 0 (hs 0 (hp₁.2 0 a))
    | .succ i =>
      rwa [Nat.nsmul_eq_mul, Nat.nsmul_eq_mul, mul_left_inj' i.succ_ne_zero] at h
  · simp only [mem_filter, mem_cut, mem_univ, exists_prop, true_and_iff, and_assoc]
    rintro f ⟨hf₁, hf₂, hf₃⟩
    refine' ⟨⟨∑ i in s, Multiset.replicate (f i / i) i, _, _⟩, _, _, _⟩
    · intro i hi
      simp only [exists_prop, mem_sum, mem_map, Function.Embedding.coeFn_mk] at hi
      rcases hi with ⟨t, ht, z⟩
      apply hs
      rwa [Multiset.eq_of_mem_replicate z]
    · simp_rw [Multiset.sum_sum, Multiset.sum_replicate, Nat.nsmul_eq_mul, ← hf₁]
      refine' sum_congr rfl fun i hi => Nat.div_mul_cancel _
      rcases hf₃ i hi with ⟨w, _, hw₂⟩
      rw [← hw₂]
      exact dvd_mul_left _ _
    · intro i
      simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq]
      split_ifs with h
      · rcases hf₃ i h with ⟨w, hw₁, hw₂⟩
        rwa [← hw₂, Nat.mul_div_cancel _ (hs i h)]
      · exact hc _ h
    · intro i hi
      rw [mem_sum] at hi
      rcases hi with ⟨j, hj₁, hj₂⟩
      rwa [Multiset.eq_of_mem_replicate hj₂]
    · ext i
      simp_rw [Multiset.count_sum', Multiset.count_replicate, sum_ite_eq]
      split_ifs with h
      · apply Nat.div_mul_cancel
        rcases hf₃ i h with ⟨w, _, hw₂⟩
        apply Dvd.intro_left _ hw₂
      · rw [zero_smul, hf₂ i h]
#align theorems_100.partial_gf_prop Theorems100.partialGF_prop

theorem partialOddGF_prop [Field α] (n m : ℕ) :
    (Finset.card
          ((univ : Finset (Nat.Partition n)).filter fun p =>
            ∀ j ∈ p.parts, j ∈ (range m).map mkOdd) :
        α) =
      coeff α n (partialOddGF m) := by
  rw [partialOddGF]
  convert partialGF_prop α n
    ((range m).map mkOdd) _ (fun _ => Set.univ) (fun _ _ => trivial) using 2
  · congr
    simp only [true_and_iff, forall_const, Set.mem_univ]
  · rw [Finset.prod_map]
    simp_rw [num_series']
    congr! 2 with x
    ext k
    constructor
    · rintro ⟨p, rfl⟩
      refine' ⟨p, ⟨⟩, _⟩
      apply mul_comm
    rintro ⟨a_w, -, rfl⟩
    apply Dvd.intro_left a_w rfl
  · intro i
    rw [mem_map]
    rintro ⟨a, -, rfl⟩
    exact Nat.succ_pos _
#align theorems_100.partial_odd_gf_prop Theorems100.partialOddGF_prop

/-- If m is big enough, the partial product's coefficient counts the number of odd partitions -/
theorem oddGF_prop [Field α] (n m : ℕ) (h : n < m * 2) :
    (Finset.card (Nat.Partition.odds n) : α) = coeff α n (partialOddGF m) := by
  rw [← partialOddGF_prop, Nat.Partition.odds]
  congr with p
  apply ball_congr
  intro i hi
  have hin : i ≤ n := by
    simpa [p.parts_sum] using Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hi
  simp only [mkOdd, exists_prop, mem_range, Function.Embedding.coeFn_mk, mem_map]
  constructor
  · intro hi₂
    have := Nat.mod_add_div i 2
    rw [Nat.not_even_iff] at hi₂
    rw [hi₂, add_comm] at this
    refine' ⟨i / 2, _, this⟩
    rw [Nat.div_lt_iff_lt_mul zero_lt_two]
    exact lt_of_le_of_lt hin h
  · rintro ⟨a, -, rfl⟩
    rw [even_iff_two_dvd]
    apply Nat.two_not_dvd_two_mul_add_one
#align theorems_100.odd_gf_prop Theorems100.oddGF_prop

theorem partialDistinctGF_prop [CommSemiring α] (n m : ℕ) :
    (Finset.card
          ((univ : Finset (Nat.Partition n)).filter fun p =>
            p.parts.Nodup ∧ ∀ j ∈ p.parts, j ∈ (range m).map ⟨Nat.succ, Nat.succ_injective⟩) :
        α) =
      coeff α n (partialDistinctGF m) := by
  rw [partialDistinctGF]
  convert partialGF_prop α n
    ((range m).map ⟨Nat.succ, Nat.succ_injective⟩) _ (fun _ => {0, 1}) (fun _ _ => Or.inl rfl)
    using 2
  · congr
    congr! with p
    rw [Multiset.nodup_iff_count_le_one]
    congr! with i
    rcases Multiset.count i p.parts with (_ | _ | ms) <;> simp
  · simp_rw [Finset.prod_map, two_series]
    congr with i
    simp [Set.image_pair]
  · simp only [mem_map, Function.Embedding.coeFn_mk]
    rintro i ⟨_, _, rfl⟩
    apply Nat.succ_pos
#align theorems_100.partial_distinct_gf_prop Theorems100.partialDistinctGF_prop

/-- If m is big enough, the partial product's coefficient counts the number of distinct partitions
-/
theorem distinctGF_prop [CommSemiring α] (n m : ℕ) (h : n < m + 1) :
    ((Nat.Partition.distincts n).card : α) = coeff α n (partialDistinctGF m) := by
  erw [← partialDistinctGF_prop, Nat.Partition.distincts]
  congr with p
  apply (and_iff_left _).symm
  intro i hi
  have : i ≤ n := by
    simpa [p.parts_sum] using Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hi
  simp only [mkOdd, exists_prop, mem_range, Function.Embedding.coeFn_mk, mem_map]
  refine' ⟨i - 1, _, Nat.succ_pred_eq_of_pos (p.parts_pos hi)⟩
  rw [tsub_lt_iff_right (Nat.one_le_iff_ne_zero.mpr (p.parts_pos hi).ne')]
  exact lt_of_le_of_lt this h
#align theorems_100.distinct_gf_prop Theorems100.distinctGF_prop

/-- The key proof idea for the partition theorem, showing that the generating functions for both
sequences are ultimately the same (since the factor converges to 0 as m tends to infinity).
It's enough to not take the limit though, and just consider large enough `m`.
-/
theorem same_gf [Field α] (m : ℕ) :
    (partialOddGF m * (range m).prod fun i => 1 - (X : PowerSeries α) ^ (m + i + 1)) =
      partialDistinctGF m := by
  rw [partialOddGF, partialDistinctGF]
  induction' m with m ih
  · simp
  rw [Nat.succ_eq_add_one]
  set! π₀ : PowerSeries α := ∏ i in range m, (1 - X ^ (m + 1 + i + 1)) with hπ₀
  set! π₁ : PowerSeries α := ∏ i in range m, (1 - X ^ (2 * i + 1))⁻¹ with hπ₁
  set! π₂ : PowerSeries α := ∏ i in range m, (1 - X ^ (m + i + 1)) with hπ₂
  set! π₃ : PowerSeries α := ∏ i in range m, (1 + X ^ (i + 1)) with hπ₃
  rw [← hπ₃] at ih
  have h : constantCoeff α (1 - X ^ (2 * m + 1)) ≠ 0 := by
    rw [RingHom.map_sub, RingHom.map_pow, constantCoeff_one, constantCoeff_X,
      zero_pow (2 * m).succ_pos, sub_zero]
    exact one_ne_zero
  calc
    (∏ i in range (m + 1), (1 - X ^ (2 * i + 1))⁻¹) *
          ∏ i in range (m + 1), (1 - X ^ (m + 1 + i + 1)) =
        π₁ * (1 - X ^ (2 * m + 1))⁻¹ * (π₀ * (1 - X ^ (m + 1 + m + 1))) := by
      rw [prod_range_succ _ m, ← hπ₁, prod_range_succ _ m, ← hπ₀]
    _ = π₁ * (1 - X ^ (2 * m + 1))⁻¹ * (π₀ * ((1 + X ^ (m + 1)) * (1 - X ^ (m + 1)))) := by
      rw [← sq_sub_sq, one_pow, add_assoc _ m 1, ← two_mul (m + 1), pow_mul']
    _ = π₀ * (1 - X ^ (m + 1)) * (1 - X ^ (2 * m + 1))⁻¹ * (π₁ * (1 + X ^ (m + 1))) := by ring
    _ =
        (∏ i in range (m + 1), (1 - X ^ (m + 1 + i))) * (1 - X ^ (2 * m + 1))⁻¹ *
          (π₁ * (1 + X ^ (m + 1))) := by
      rw [prod_range_succ', add_zero, hπ₀]; simp_rw [← add_assoc]
    _ = π₂ * (1 - X ^ (m + 1 + m)) * (1 - X ^ (2 * m + 1))⁻¹ * (π₁ * (1 + X ^ (m + 1))) := by
      rw [add_right_comm, hπ₂, ← prod_range_succ]; simp_rw [add_right_comm]
    _ = π₂ * (1 - X ^ (2 * m + 1)) * (1 - X ^ (2 * m + 1))⁻¹ * (π₁ * (1 + X ^ (m + 1))) := by
      rw [two_mul, add_right_comm _ m 1]
    _ = (1 - X ^ (2 * m + 1)) * (1 - X ^ (2 * m + 1))⁻¹ * π₂ * (π₁ * (1 + X ^ (m + 1))) := by ring
    _ = π₂ * (π₁ * (1 + X ^ (m + 1))) := by rw [PowerSeries.mul_inv_cancel _ h, one_mul]
    _ = π₁ * π₂ * (1 + X ^ (m + 1)) := by ring
    _ = π₃ * (1 + X ^ (m + 1)) := by rw [ih]
    _ = _ := by rw [prod_range_succ]
#align theorems_100.same_gf Theorems100.same_gf

theorem same_coeffs [Field α] (m n : ℕ) (h : n ≤ m) :
    coeff α n (partialOddGF m) = coeff α n (partialDistinctGF m) := by
  rw [← same_gf, coeff_mul_prod_one_sub_of_lt_order]
  rintro i -
  rw [order_X_pow]
  exact mod_cast Nat.lt_succ_of_le (le_add_right h)
#align theorems_100.same_coeffs Theorems100.same_coeffs

theorem partition_theorem (n : ℕ) :
    (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card := by
  -- We need the counts to live in some field (which contains ℕ), so let's just use ℚ
  suffices ((Nat.Partition.odds n).card : ℚ) = (Nat.Partition.distincts n).card from
    mod_cast this
  rw [distinctGF_prop n (n + 1) (by linarith)]
  rw [oddGF_prop n (n + 1) (by linarith)]
  apply same_coeffs (n + 1) n n.le_succ
#align theorems_100.partition_theorem Theorems100.partition_theorem

end

end Theorems100
