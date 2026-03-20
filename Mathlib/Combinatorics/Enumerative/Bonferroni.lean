/-
Copyright (c) 2026 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
import Mathlib.Data.Nat.Choose.Sum

/-!
# Bonferroni inequalities

This file proves the Bonferroni inequalities, i.e. the alternating upper and lower bounds obtained
by truncating the inclusion–exclusion formula for a finite union of sets.

## Main results

* `Finset.indicator_biUnion_le_bonferroniIndicator_of_odd`: for odd `k`, the indicator of the
  union is at most the truncated indicator.
* `Finset.bonferroniIndicator_le_indicator_biUnion_of_even`: for even `k`, the truncated
  indicator is at most the indicator of the union.
* `Finset.card_biUnion_le_bonferroniCard_of_odd`: for odd `k`, the cardinality of the union is
  at most the truncated sum.
* `Finset.bonferroniCard_le_card_biUnion_of_even`: for even `k`, the truncated sum is at most
  the cardinality of the union.
-/

open Nat Int Set

/-! ### Binomial identities -/

section Binomial

open Finset

/-- The truncated alternating binomial sum equals `1 - (-1) ^ k * (m - 1).choose k`
when `k < m`. -/
private lemma trunc_choose_sum_eq_one_sub (m k : ℕ) (hk : k < m) :
    (∑ j ∈ Finset.Icc 1 k, ((-1 : ℤ) ^ (j + 1)) * (choose m j)) =
    1 - ((-1 : ℤ) ^ k) * (choose (m - 1) k) := by
  simp only [show ∀ j : ℕ, ((-1 : ℤ) ^ (j + 1)) = -((-1 : ℤ) ^ j) from fun j ↦ by ring,
    neg_mul, sum_neg_distrib]
  simp only [reduceNeg, neg_eq_iff_eq_neg, neg_sub]
  have insert_eq : range (k + 1) = insert 0 (Finset.Icc 1 k) := by grind
  calc
    _ = (∑ j ∈ range (k + 1), ((-1 : ℤ) ^ j) * (choose m j)) - 1 := by simp [insert_eq]
    _ = (∑ j ∈ range (k + 1), ((-1 : ℤ) ^ j) * (choose ((m - 1) + 1) j)) - 1 := by grind
    _ = _ := by rw [alternating_sum_range_choose_eq_choose]

/-- The full alternating binomial sum equals `1` when `1 ≤ m`. -/
private lemma full_choose_sum_eq_one (m : ℕ) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.Icc 1 m, ((-1 : ℤ) ^ (j + 1)) * (choose m j)) = 1 := by
  simp only [show ∀ j : ℕ, ((-1 : ℤ) ^ (j + 1)) = -((-1 : ℤ) ^ j) from fun j ↦ by ring,
    neg_mul, sum_neg_distrib]
  suffices ∑ j ∈ Icc 1 m, ((-1 : ℤ) ^ j) * (choose m j) = -1 by linarith
  have insert_eq : range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    rw [congr_fun range_eq_Ico (m + 1), ← Finset.Ico_succ_right_eq_Icc 1 m,
        ← Finset.insert_Ico_succ_left_eq_Ico (zero_lt_succ m)]
    simp
  calc
    _ = (∑ j ∈ range (m + 1), ((-1 : ℤ) ^ j) * (choose m j)) - 1 := by simp [insert_eq]
    _ = _ := by grind [alternating_sum_range_choose_of_ne]

/-- The truncated alternating binomial sum is `≥ 1` when `k` is odd and `≤ 1` when `k` is even,
provided `1 ≤ m`. -/
private lemma trunc_choose_sum_bounds (m k : ℕ) (hm : 1 ≤ m) :
    (Odd k → 1 ≤ ∑ j ∈ Finset.Icc 1 (min k m), ((-1 : ℤ) ^ (j + 1)) * (choose m j)) ∧
    (Even k → (∑ j ∈ Finset.Icc 1 (min k m), ((-1 : ℤ) ^ (j + 1)) * (choose m j)) ≤ 1) := by
  by_cases! hkm : k < m
  · constructor
    all_goals
      intro hk
      rw [min_eq_left hkm.le, trunc_choose_sum_eq_one_sub m k hkm]
      simp [hk.neg_one_pow]
  · constructor
    all_goals
      intro hk
      rw [min_eq_right hkm, full_choose_sum_eq_one m hm]

end Binomial

namespace Finset

variable {ι α : Type*}

/-! ### Truncated powerset -/

section TruncPowerset

variable {s t : Finset ι} {k : ℕ}

/-- `s.truncPowerset k` is the finset of nonempty subsets of `s` whose cardinality is at
most `k`. -/
def truncPowerset (s : Finset ι) (k : ℕ) : Finset (Finset ι) :=
  s.powerset.filter (fun t ↦ t.Nonempty ∧ #t ≤ k)

@[simp]
theorem mem_truncPowerset : t ∈ s.truncPowerset k ↔ t ⊆ s ∧ t.Nonempty ∧ #t ≤ k := by
  simp [truncPowerset]

theorem truncPowerset_nonempty (ht : t ∈ s.truncPowerset k) : t.Nonempty := by
  rw [mem_truncPowerset] at ht
  exact ht.2.1

private lemma truncPowerset_eq_filter_nonempty (hk : #s ≤ k) :
    s.truncPowerset k = s.powerset.filter Finset.Nonempty := by
  ext t
  simp only [truncPowerset, mem_filter, mem_powerset]
  constructor
  · grind
  · intro ⟨h1, h2⟩
    exact ⟨h1, h2, (card_le_card h1).trans hk⟩

private lemma truncPowerset_stabilize {k₁ k₂ : ℕ} (h₁ : #s ≤ k₁) (h₂ : #s ≤ k₂) :
    s.truncPowerset k₁ = s.truncPowerset k₂ := by
  rw [truncPowerset_eq_filter_nonempty h₁, truncPowerset_eq_filter_nonempty h₂]

end TruncPowerset

/-! ### Pointwise indicator inequalities -/

section IndicatorBonferroni

variable (s : Finset ι) (S : ι → Set α)

/-- The truncated inclusion–exclusion indicator at a point `a`, defined as
`∑ t ∈ s.truncPowerset k, (-1) ^ (#t + 1) * (⋂ i ∈ t, S i).indicator 1 a`. -/
noncomputable def bonferroniIndicator (k : ℕ) (a : α) : ℤ :=
  ∑ t ∈ s.truncPowerset k, ((-1 : ℤ) ^ (#t + 1)) * ((⋂ i ∈ t, S i).indicator 1 a)

private lemma bonferroniIndicator_eq_zero (k : ℕ) (a : α) (ha : a ∉ ⋃ i ∈ s, S i) :
    bonferroniIndicator s S k a = 0 := by
  unfold bonferroniIndicator
  apply Finset.sum_eq_zero
  intro t ht
  rw [mem_truncPowerset] at ht
  have : a ∉ ⋂ i ∈ t, S i := by
    intro hmem
    apply ha
    obtain ⟨i, hi⟩ := ht.2.1
    exact mem_iUnion₂.mpr ⟨i, ht.1 hi, mem_iInter₂.mp hmem i hi⟩
  rw [indicator_of_notMem this, mul_zero]

private lemma bonferroniIndicator_eq_trunc_choose_sum (k : ℕ) (a : α) (ha : a ∈ ⋃ i ∈ s, S i) :
    ∃ (m : ℕ), 1 ≤ m ∧ bonferroniIndicator s S k a =
      ∑ j ∈ Icc 1 (min k m), (-1 : ℤ) ^ (j + 1) * (Nat.choose m j) := by
  classical
  unfold bonferroniIndicator
  set T := s.filter (fun i ↦ a ∈ S i)
  have hT_sub : T ⊆ s := filter_subset _ s
  have hT_nonempty : T.Nonempty := by
    obtain ⟨i, his, hia⟩ := mem_iUnion₂.mp ha
    exact ⟨i, mem_filter.mpr ⟨his, hia⟩⟩
  refine ⟨#T, hT_nonempty.card_pos, ?_⟩
  have mem_inter_iff : ∀ t, t ⊆ s → (a ∈ ⋂ i ∈ t, S i ↔ t ⊆ T) := by
    intro t hts
    simp only [mem_iInter]
    grind
  have term_eq : ∀ t ∈ s.truncPowerset k,
      (-1 : ℤ) ^ (#t + 1) * (⋂ i ∈ t, S i).indicator 1 a =
      if t ⊆ T then (-1 : ℤ) ^ (#t + 1) else 0 := by
    intro t ht
    rw [mem_truncPowerset] at ht
    by_cases htT : t ⊆ T
    · rw [indicator_of_mem ((mem_inter_iff t ht.1).mpr htT), Pi.one_apply, mul_one, if_pos htT]
    · rw [indicator_of_notMem (mt (mem_inter_iff t ht.1).mp htT), mul_zero, if_neg htT]
  have filter_eq : (s.truncPowerset k).filter (· ⊆ T) = T.truncPowerset k := by
    ext t
    simp [mem_filter, mem_truncPowerset]
    grind
  have trunc_eq : T.truncPowerset k =
      (Icc 1 (min k #T)).biUnion (fun j ↦ T.powersetCard j) := by
    ext t
    simp only [mem_biUnion, mem_Icc, mem_powersetCard, mem_truncPowerset]
    constructor
    · intro ⟨htT, hne, hcard⟩
      exact ⟨#t, ⟨hne.card_pos, le_min hcard (card_le_card htT)⟩, htT, rfl⟩
    · intro ⟨j, ⟨hj1, hjk⟩, htT, hjt⟩
      rw [← hjt] at hj1 hjk
      exact ⟨htT, card_pos.mp hj1, (le_min_iff.mp hjk).1⟩
  have disj : (Icc 1 (min k #T) : Set ℕ).PairwiseDisjoint
      (fun j ↦ T.powersetCard j) := by
    intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro t hi hj
    rw [mem_powersetCard] at hi hj
    omega
  calc
    _ = ∑ t ∈ T.truncPowerset k, (-1 : ℤ) ^ (#t + 1) := by
      rw [← filter_eq, sum_filter]
      exact sum_congr rfl term_eq
    _ = ∑ j ∈ Icc 1 (min k #T),
          ∑ t ∈ T.powersetCard j, (-1 : ℤ) ^ (#t + 1) := by
      rw [trunc_eq, sum_biUnion disj]
    _ = _ := by
      apply sum_congr rfl
      intro j _
      have card_eq : ∀ t ∈ T.powersetCard j, #t = j := fun t ht ↦ (mem_powersetCard.mp ht).2
      rw [sum_congr rfl (fun t ht ↦ by rw [card_eq t ht]),
          sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]

private lemma bonferroniIndicator_bounds (k : ℕ) (a : α) :
    (Odd k → ((⋃ i ∈ s, S i).indicator 1 a : ℤ) ≤ bonferroniIndicator s S k a) ∧
    (Even k → bonferroniIndicator s S k a ≤ ((⋃ i ∈ s, S i).indicator 1 a : ℤ)) := by
  by_cases ha : a ∈ ⋃ i ∈ s, S i
  · simp only [indicator_of_mem ha, Pi.one_apply]
    obtain ⟨m, hm, heq⟩ := bonferroniIndicator_eq_trunc_choose_sum s S k a ha
    simp only [heq]
    exact trunc_choose_sum_bounds m k hm
  · simp [indicator_of_notMem ha, bonferroniIndicator_eq_zero s S k a ha]

/-- **Bonferroni inequality**, upper bound. For odd `k`, the truncated inclusion–exclusion
indicator is at least the indicator of `⋃ i ∈ s, S i`. -/
theorem indicator_biUnion_le_bonferroniIndicator_of_odd (k : ℕ) (hk : Odd k) (a : α) :
    ((⋃ i ∈ s, S i).indicator 1 a : ℤ) ≤ bonferroniIndicator s S k a :=
  (bonferroniIndicator_bounds s S k a).1 hk

/-- **Bonferroni inequality**, lower bound. For even `k`, the truncated inclusion–exclusion
indicator is at most the indicator of `⋃ i ∈ s, S i`. -/
theorem bonferroniIndicator_le_indicator_biUnion_of_even (k : ℕ) (hk : Even k) (a : α) :
    bonferroniIndicator s S k a ≤ ((⋃ i ∈ s, S i).indicator 1 a : ℤ) :=
  (bonferroniIndicator_bounds s S k a).2 hk

private lemma bonferroniIndicator_congr (k₁ k₂ : ℕ) (h₁ : #s ≤ k₁) (h₂ : #s ≤ k₂) (a : α) :
    bonferroniIndicator s S k₁ a = bonferroniIndicator s S k₂ a := by
  simp_rw [bonferroniIndicator, truncPowerset_stabilize h₁ h₂]

/-- When `#s ≤ k`, the truncated inclusion–exclusion indicator equals the indicator of the
union. -/
theorem bonferroniIndicator_eq_indicator_biUnion_of_card_le (k : ℕ) (hk : #s ≤ k) (a : α) :
    bonferroniIndicator s S k a = (⋃ i ∈ s, S i).indicator 1 a := by
  apply le_antisymm
  · rw [bonferroniIndicator_congr s S k (2 * #s) hk (by omega) a]
    exact bonferroniIndicator_le_indicator_biUnion_of_even s S _ ⟨#s, by ring⟩ a
  · rw [bonferroniIndicator_congr s S k (2 * #s + 1) hk (by omega) a]
    exact indicator_biUnion_le_bonferroniIndicator_of_odd s S _ ⟨#s, rfl⟩ a

end IndicatorBonferroni

/-! ### Cardinality bounds -/

section CardinalityBonferroni

variable [DecidableEq α] {s : Finset ι} {S : ι → Finset α}

/-- The truncated inclusion–exclusion sum of intersection cardinalities, over nonempty subsets of
`s` with at most `k` elements. This is the cardinality analogue of `bonferroniIndicator`. -/
def bonferroniCard (s : Finset ι) (S : ι → Finset α) (k : ℕ) : ℤ :=
  ∑ t : s.truncPowerset k,
    (-1 : ℤ) ^ (#(t : Finset ι) + 1) * #((t : Finset ι).inf' (truncPowerset_nonempty t.2) S)

private lemma mem_iUnion_of_mem_biUnion {a : α} (ha : a ∈ s.biUnion S) :
    a ∈ ⋃ i ∈ s, (↑(S i) : Set α) := by
  obtain ⟨i, hi, hia⟩ := mem_biUnion.mp ha
  exact mem_iUnion₂.mpr ⟨i, hi, hia⟩

private lemma card_inf'_eq_sum_indicator {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    (#(t.inf' ht S) : ℤ) =
      ∑ a ∈ s.biUnion S, (⋂ i ∈ t, (↑(S i) : Set α)).indicator (1 : α → ℤ) a := by
  have hmem : ∀ a, a ∈ ⋂ i ∈ t, (↑(S i) : Set α) ↔ a ∈ t.inf' ht S := by
    intro a; simp [mem_inf', mem_iInter]
  have hsub : t.inf' ht S ⊆ s.biUnion S := by
    intro a ha; obtain ⟨i, hi⟩ := ht
    rw [mem_inf'] at ha
    exact mem_biUnion.mpr ⟨i, hts hi, ha i hi⟩
  calc (#(t.inf' ht S) : ℤ)
      = ∑ a ∈ t.inf' ht S, (1 : ℤ) := by exact_mod_cast card_eq_sum_ones _
    _ = ∑ a ∈ t.inf' ht S, (⋂ i ∈ t, (↑(S i) : Set α)).indicator 1 a := by
        apply sum_congr rfl; intro a ha
        rw [indicator_of_mem ((hmem a).mpr ha), Pi.one_apply]
    _ = ∑ a ∈ s.biUnion S, (⋂ i ∈ t, (↑(S i) : Set α)).indicator 1 a := by
        apply sum_subset hsub; intro a _ ha
        exact indicator_of_notMem (mt (hmem a).mp ha) _

private lemma bonferroniCard_eq_sum_bonferroniIndicator (s : Finset ι) (S : ι → Finset α)
    (k : ℕ) : bonferroniCard s S k =
      ∑ a ∈ s.biUnion S, bonferroniIndicator s (fun i ↦ ↑(S i)) k a := by
  unfold bonferroniCard
  conv_lhs =>
    arg 2; ext t
    rw [card_inf'_eq_sum_indicator (truncPowerset_nonempty t.2) (mem_truncPowerset.mp t.2).1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext a
  rw [bonferroniIndicator]
  exact Finset.sum_coe_sort (s.truncPowerset k)
    (fun t => (-1 : ℤ) ^ (#t + 1) * (⋂ i ∈ t, (↑(S i) : Set α)).indicator 1 a)

/-- **Bonferroni inequality**, upper bound for cardinalities. For odd `k`, the cardinality of
`s.biUnion S` is at most `bonferroniCard s S k`. -/
theorem card_biUnion_le_bonferroniCard_of_odd (s : Finset ι) (S : ι → Finset α) (k : ℕ)
    (hk : Odd k) : (#(s.biUnion S) : ℤ) ≤ bonferroniCard s S k := by
  rw [bonferroniCard_eq_sum_bonferroniIndicator]
  calc
    _ = ∑ a ∈ s.biUnion S, (1 : ℤ) := by exact_mod_cast card_eq_sum_ones _
    _ ≤ ∑ a ∈ s.biUnion S, bonferroniIndicator s (fun i ↦ ↑(S i)) k a := by
      apply sum_le_sum
      intro a ha
      have := indicator_biUnion_le_bonferroniIndicator_of_odd s (fun i ↦ ↑(S i)) k hk a
      rwa [indicator_of_mem (mem_iUnion_of_mem_biUnion ha), Pi.one_apply] at this

/-- **Bonferroni inequality**, lower bound for cardinalities. For even `k`,
`bonferroniCard s S k` is at most the cardinality of `s.biUnion S`. -/
theorem bonferroniCard_le_card_biUnion_of_even (s : Finset ι) (S : ι → Finset α) (k : ℕ)
    (hk : Even k) : bonferroniCard s S k ≤ (#(s.biUnion S) : ℤ) := by
  rw [bonferroniCard_eq_sum_bonferroniIndicator]
  calc
    _ ≤ ∑ a ∈ s.biUnion S, (1 : ℤ) := by
      apply sum_le_sum
      intro a ha
      have := bonferroniIndicator_le_indicator_biUnion_of_even s (fun i ↦ ↑(S i)) k hk a
      rwa [indicator_of_mem (mem_iUnion_of_mem_biUnion ha), Pi.one_apply] at this
    _ = _ := by exact_mod_cast (card_eq_sum_ones _).symm

/-- When `#s ≤ k`, the truncated inclusion–exclusion cardinality sum equals the cardinality of
`s.biUnion S`. -/
theorem card_biUnion_eq_bonferroniCard_of_card_le (s : Finset ι) (S : ι → Finset α) (k : ℕ)
    (hk : #s ≤ k) : (#(s.biUnion S) : ℤ) = bonferroniCard s S k := by
  rw [bonferroniCard_eq_sum_bonferroniIndicator]
  calc
    _ = ∑ a ∈ s.biUnion S, (1 : ℤ) := by exact_mod_cast card_eq_sum_ones _
    _ = ∑ a ∈ s.biUnion S, bonferroniIndicator s (fun i ↦ ↑(S i)) k a := by
      apply sum_congr rfl
      intro a ha
      have := bonferroniIndicator_eq_indicator_biUnion_of_card_le s (fun i ↦ ↑(S i)) k hk a
      rw [indicator_of_mem (mem_iUnion_of_mem_biUnion ha), Pi.one_apply] at this
      exact this.symm

end CardinalityBonferroni

end Finset
