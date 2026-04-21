/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.ChevalleyWarning

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * n - 1` elements of `ZMod n`, we can find `n`
elements of sum zero.

## Main declarations

* `Int.erdos_ginzburg_ziv`: The Erdős–Ginzburg–Ziv theorem stated using sequences in `ℤ`
* `ZMod.erdos_ginzburg_ziv`: The Erdős–Ginzburg–Ziv theorem stated using sequences in `ZMod n`
-/
set_option backward.defeqAttrib.useBackward true

public section

open Finset MvPolynomial

variable {ι : Type*}

section prime
variable {p : ℕ} [Fact p.Prime] {s : Finset ι}

set_option linter.unusedVariables false in
/-- The first multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₁ (s : Finset ι) (a : ι → ZMod p) : MvPolynomial s (ZMod p) :=
  ∑ i, X i ^ (p - 1)

/-- The second multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₂ (s : Finset ι) (a : ι → ZMod p) : MvPolynomial s (ZMod p) :=
  ∑ i : s, a i • X i ^ (p - 1)

private lemma totalDegree_f₁_add_totalDegree_f₂ {a : ι → ZMod p} :
    (f₁ s a).totalDegree + (f₂ s a).totalDegree < 2 * p - 1 := by
  calc
    _ ≤ (p - 1) + (p - 1) := by
      gcongr <;> apply totalDegree_finsetSum_le <;> rintro i _
      · exact (totalDegree_X_pow ..).le
      · exact (totalDegree_smul_le ..).trans (totalDegree_X_pow ..).le
    _ < 2 * p - 1 := by have := (Fact.out : p.Prime).two_le; lia

/-- The prime case of the **Erdős–Ginzburg–Ziv theorem** for `ℤ/pℤ`.

Any sequence of `2 * p - 1` elements of `ZMod p` contains a subsequence of `p` elements whose sum is
zero. -/
private theorem ZMod.erdos_ginzburg_ziv_prime (a : ι → ZMod p) (hs : #s = 2 * p - 1) :
    ∃ t ⊆ s, #t = p ∧ ∑ i ∈ t, a i = 0 := by
  haveI : NeZero p := inferInstance
  classical
  -- Let `N` be the number of common roots of our polynomials `f₁` and `f₂` (`f s ff` and `f s tt`).
  set N := Fintype.card {x // eval x (f₁ s a) = 0 ∧ eval x (f₂ s a) = 0}
  -- Zero is a common root to `f₁` and `f₂`, so `N` is nonzero
  let zero_sol : {x // eval x (f₁ s a) = 0 ∧ eval x (f₂ s a) = 0} :=
    ⟨0, by simp [f₁, f₂, map_sum, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]⟩
  have hN₀ : 0 < N := @Fintype.card_pos _ _ ⟨zero_sol⟩
  have hs' : 2 * p - 1 = Fintype.card s := by simp [hs]
  -- Chevalley-Warning gives us that `p ∣ n` because the total degrees of `f₁` and `f₂` are at most
  -- `p - 1`, and we have `2 * p - 1 > 2 * (p - 1)` variables.
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p
    (totalDegree_f₁_add_totalDegree_f₂.trans_eq hs')
  -- Hence, `2 ≤ p ≤ N` and we can make a common root `x ≠ 0`.
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card ((Fact.out : p.Prime).one_lt.trans_le <|
    Nat.le_of_dvd hN₀ hpN) zero_sol
  -- This common root gives us the required subsequence, namely the `i ∈ s` such that `x i ≠ 0`.
  refine ⟨({a | x.1 a ≠ 0} : Finset _).map ⟨(↑), Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · simp +contextual [subset_iff]
  -- From `f₁ x = 0`, we get that `p` divides the number of `a` such that `x a ≠ 0`.
  · rw [card_map]
    refine Nat.eq_of_dvd_of_lt_two_mul (Finset.card_pos.2 ?_).ne' ?_ <|
      (Finset.card_filter_le _ _).trans_lt ?_
    -- This number is nonzero because `x ≠ 0`.
    · rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
      exact hx.imp (fun a ha ↦ mem_filter.2 ⟨Finset.mem_attach _ _, ha⟩)
    · rw [← CharP.cast_eq_zero_iff (ZMod p), ← Finset.sum_boole]
      simpa only [f₁, map_sum, ZMod.pow_card_sub_one, map_pow, eval_X] using x.2.1
    -- And it is at most `2 * p - 1`, so it must be `p`.
    · rw [univ_eq_attach, card_attach, hs]
      exact tsub_lt_self (mul_pos zero_lt_two (Fact.out : p.Prime).pos) zero_lt_one
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  · simpa [f₂, ZMod.pow_card_sub_one, Finset.sum_filter] using x.2.2

/-- The prime case of the **Erdős–Ginzburg–Ziv theorem** for `ℤ`.

Any sequence of `2 * p - 1` elements of `ℤ` contains a subsequence of `p` elements whose sum is
divisible by `p`. -/
private theorem Int.erdos_ginzburg_ziv_prime (a : ι → ℤ) (hs : #s = 2 * p - 1) :
    ∃ t ⊆ s, #t = p ∧ ↑p ∣ ∑ i ∈ t, a i := by
  simpa [← Int.cast_sum, ZMod.intCast_zmod_eq_zero_iff_dvd]
    using ZMod.erdos_ginzburg_ziv_prime (Int.cast ∘ a) hs

end prime

section composite
variable {n : ℕ} {s : Finset ι}

/-- The **Erdős–Ginzburg–Ziv theorem** for `ℤ`.

Any sequence of at least `2 * n - 1` elements of `ℤ` contains a subsequence of `n` elements whose
sum is divisible by `n`. -/
theorem Int.erdos_ginzburg_ziv (a : ι → ℤ) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ↑n ∣ ∑ i ∈ t, a i := by
  classical
  -- Do induction on the prime factorisation of `n`. Note that we will apply the induction
  -- hypothesis with `ι := Finset ι`, so we need to generalise.
  induction n using Nat.prime_composite_induction generalizing ι with
  -- When `n := 0`, we can set `t := ∅`.
  | zero => exact ⟨∅, by simp⟩
  -- When `n := 1`, we can take `t` to be any subset of `s` of size `2 * n - 1`.
  | one => simpa using exists_subset_card_eq hs
  -- When `n := p` is prime, we use the prime case `Int.erdos_ginzburg_ziv_prime`.
  | prime p hp =>
    haveI := Fact.mk hp
    obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hs
    obtain ⟨u, hut, hu⟩ := Int.erdos_ginzburg_ziv_prime a ht
    exact ⟨u, hut.trans hts, hu⟩
  -- When `n := m * n` is composite, we pick (by induction hypothesis on `n`) `2 * m - 1` sets of
  -- size `n` and sums divisible by `n`. Then by induction hypothesis (on `m`) we can pick `m` of
  -- these sets whose sum is divisible by `m * n`.
  | composite m hm ihm n hn ihn =>
     -- First, show that it is enough to have those `2 * m - 1` sets.
    suffices ∀ k ≤ 2 * m - 1, ∃ 𝒜 : Finset (Finset ι), #𝒜 = k ∧
      (𝒜 : Set (Finset ι)).Pairwise _root_.Disjoint ∧
        ∀ ⦃t⦄, t ∈ 𝒜 → t ⊆ s ∧ #t = n ∧ ↑n ∣ ∑ i ∈ t, a i by
     -- Assume `𝒜` is a family of `2 * m - 1` sets, each of size `n` and sum divisible by `n`.
      obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ := this _ le_rfl
      -- By induction hypothesis on `m`, find a subfamily `ℬ` of size `m` such that the sum over
      -- `t ∈ ℬ` of `(∑ i ∈ t, a i) / n` is divisible by `m`.
      obtain ⟨ℬ, hℬ𝒜, hℬcard, hℬ⟩ := ihm (fun t ↦ (∑ i ∈ t, a i) / n) h𝒜card.ge
      -- We are done.
      refine ⟨ℬ.biUnion fun x ↦ x, biUnion_subset.2 fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).1, ?_, ?_⟩
      · rw [card_biUnion (h𝒜disj.mono hℬ𝒜), sum_const_nat fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.1, hℬcard]
      rwa [sum_biUnion, Int.natCast_mul, mul_comm, ← Int.dvd_div_iff_mul_dvd, Int.sum_div]
      · exact fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.2
      · exact dvd_sum fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.2
      · exact h𝒜disj.mono hℬ𝒜
    -- Now, let's find those `2 * m - 1` sets.
    rintro k hk
    -- We induct on the size `k ≤ 2 * m - 1` of the family we are constructing.
    induction k with
    -- For `k = 0`, the empty family trivially works.
    | zero => exact ⟨∅, by simp⟩
    | succ k ih =>
    -- At `k + 1`, call `𝒜` the existing family of size `k ≤ 2 * m - 2`.
    obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ := ih (Nat.le_of_succ_le hk)
    -- There are at least `2 * (m * n) - 1 - k * n ≥ 2 * m - 1` elements in `s` that have not been
    -- taken in any element of `𝒜`.
    have : 2 * n - 1 ≤ #(s \ 𝒜.biUnion id) := by
      calc
        _ ≤ (2 * m - k) * n - 1 := by gcongr; lia
        _ = (2 * (m * n) - 1) - ∑ t ∈ 𝒜, #t := by
          rw [tsub_mul, mul_assoc, tsub_right_comm, sum_const_nat fun t ht ↦ (h𝒜 ht).2.1, h𝒜card]
        _ ≤ #s - #(𝒜.biUnion id) := by gcongr; exact card_biUnion_le
        _ ≤ #(s \ 𝒜.biUnion id) := le_card_sdiff ..
    -- So by the induction hypothesis on `n` we can find a new set `t` of size `n` and sum divisible
    -- by `n`.
    obtain ⟨t₀, ht₀, ht₀card, ht₀sum⟩ := ihn a this
    -- This set is distinct and disjoint from the previous ones, so we are done.
    have : t₀ ∉ 𝒜 := by
      rintro h
      obtain rfl : n = 0 := by
        simpa [← card_eq_zero, ht₀card] using sdiff_disjoint.mono ht₀ <| subset_biUnion_of_mem id h
      lia
    refine ⟨𝒜.cons t₀ this, by rw [card_cons, h𝒜card], ?_, ?_⟩
    · simp only [cons_eq_insert, coe_insert, Set.pairwise_insert_of_symmetric symmetric_disjoint,
        mem_coe, ne_eq]
      exact ⟨h𝒜disj, fun t ht _ ↦ sdiff_disjoint.mono ht₀ <| subset_biUnion_of_mem id ht⟩
    · simp only [cons_eq_insert, mem_insert, forall_eq_or_imp, and_assoc]
      exact ⟨ht₀.trans sdiff_subset, ht₀card, ht₀sum, h𝒜⟩

/-- The **Erdős–Ginzburg–Ziv theorem** for `ℤ/nℤ`.

Any sequence of at least `2 * n - 1` elements of `ZMod n` contains a subsequence of `n` elements
whose sum is zero. -/
theorem ZMod.erdos_ginzburg_ziv (a : ι → ZMod n) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0 := by
  simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd] using Int.erdos_ginzburg_ziv (ZMod.cast ∘ a) hs

/-- The **Erdős–Ginzburg–Ziv theorem** for `ℤ` for multiset.

Any multiset of at least `2 * n - 1` elements of `ℤ` contains a submultiset of `n` elements whose
sum is divisible by `n`. -/
theorem Int.erdos_ginzburg_ziv_multiset (s : Multiset ℤ) (hs : 2 * n - 1 ≤ Multiset.card s) :
    ∃ t ≤ s, Multiset.card t = n ∧ ↑n ∣ t.sum := by
  obtain ⟨t, hts, ht⟩ := Int.erdos_ginzburg_ziv (s := s.toEnumFinset) Prod.fst (by simpa using hs)
  exact ⟨t.1.map Prod.fst, Multiset.map_fst_le_of_subset_toEnumFinset hts, by simpa using ht⟩

/-- The **Erdős–Ginzburg–Ziv theorem** for `ℤ/nℤ` for multiset.

Any multiset of at least `2 * n - 1` elements of `ℤ` contains a submultiset of `n` elements whose
sum is divisible by `n`. -/
theorem ZMod.erdos_ginzburg_ziv_multiset (s : Multiset (ZMod n))
    (hs : 2 * n - 1 ≤ Multiset.card s) : ∃ t ≤ s, Multiset.card t = n ∧ t.sum = 0 := by
  obtain ⟨t, hts, ht⟩ := ZMod.erdos_ginzburg_ziv (s := s.toEnumFinset) Prod.fst (by simpa using hs)
  exact ⟨t.1.map Prod.fst, Multiset.map_fst_le_of_subset_toEnumFinset hts, by simpa using ht⟩

end composite
