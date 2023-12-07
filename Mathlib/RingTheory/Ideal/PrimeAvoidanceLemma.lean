/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Prime Avoidance Lemma

Let `R` be a commutative ring, `J` an ideal of `R`, `S` be a finite collection of ideals of `R`
such that ideals in `S` are prime ideals except for perhaps at most two.

If `J` is a subset of any of ideal in `S`, then there is an `x ∈ R` such that `x ∈ J` but `x` is
not in any of the ideals in `S`.

## Implementation details

- variable naming : `I, J, Q` are (not necessarily prime) ideals of `R`. When we need to use ideals
as index then `i, j` are used. `𝔭` is a prime ideal of `R`. `S, S'` are finite sets of ideals.

- We spell "`S` has at most 2 non-prime ideals" as `∀ S' ≤ S, 2 < S'.card → ∃ p ∈ S', p.IsPrime`.
We choose not to use `(S.filter (¬ Ideal.IsPrime)).card ≤ 2` to avoid `DecidablePred Ideal.IsPrime`
instance and it is slightly easier to use the previous version in the proof.

## TODO
* graded version
* the version where `R` contains an infinite field.

## Reference
[00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

variable {R : Type _} [CommRing R]

open BigOperators
open SetLike (coe_subset_coe)
open Finset hiding not_subset
open Set hiding mem_singleton mem_insert

lemma Finset.filter_card_le_iff {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    (s.filter P).card ≤ n ↔ ∀ s' ≤ s, n < s'.card → ∃ a ∈ s', ¬ P a := by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
    have card1 := card_le_of_subset (monotone_filter_left P hs') |>.trans H
    have card2 : (s'.filter P).card = s'.card
    · rw [filter_true_of_mem rid]
    exact lt_irrefl _ <| lt_of_lt_of_le (card2.symm ▸ s'_card) card1
  · contrapose!
    intro H
    exact ⟨s.filter P, s.filter_subset P, H, fun a ha ↦ (mem_filter.mp ha).2⟩


/--
Let `R` be a commutative ring, `J` an ideal of `R`, `S` be a finite collection of ideals of `R`
such that ideals in `S` are prime ideals except for perhaps at most two.
Then if `J` is a subset of the union of `S`, `J` is already a subset of some ideal `I` in `S`.
-/
theorem Ideal.le_of_subset_union_with_at_most_two_non_primes
    (J : Ideal R)
    (S : Finset (Ideal R))
    (exists_prime : ∀ S' ≤ S, 2 < S'.card → ∃ p ∈ S', p.IsPrime)
    (subset_union : (J : Set R) ⊆ ⋃ (I : S), I) :
    ∃ I, I ∈ S ∧ J ≤ I := by
  classical

  induction' S using Finset.strongInductionOn with S ih
  -- We perform a strong induction on `S`, i.e. we assume that for any proper subset `S'` of `S`
  -- with at most two non-prime ideals, if `J` is a subset of the union of `S'`, then `I` is a
  -- subideal of some ideal in `S'` already.

  -- We can assume without loss of generality that `S` has more than 2 ideals, for `S` with fewer
  -- ideals are easy cases.
  by_cases card : S.card ≤ 2
  · replace card : S.card = 0 ∨ S.card = 1 ∨ S.card = 2
    · interval_cases S.card <;> tauto
    obtain card|card|card := card
    · aesop
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp card
      exact ⟨i, mem_singleton_self _, fun x hx ↦ by aesop⟩
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp card
      simp only [mem_singleton, mem_insert, coe_subset_coe, exists_eq_or_imp, exists_eq_left,
        iUnion_subtype, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left] at subset_union ⊢
      exact J.le_or_le_of_subset_union _ _ subset_union

  -- We further assume that `J` is not a subset of any proper subset of `S`, for otherwise, our
  -- induction hypotheses implies the desired result already.
  -- We will show that this assumption in fact leads to a contradiction,
  -- since the goal is to produce an `I ≥ J`, such that `{I}` is a proper subset of `S`.
  by_cases subset' : ∀ S', S' ⊂ S → ¬ (J : Set R) ⊆ ⋃ (I : S'), I
  pick_goal 2
  · push_neg at subset'
    obtain ⟨S', lt, le⟩ := subset'
    obtain ⟨I, hI1, hI2⟩ := ih _ lt (fun s hs ↦ exists_prime s (hs.trans lt.1)) le
    exact ⟨I, lt.1 hI1, hI2⟩

  -- Since `S` contains more than 2 ideals, there must be a prime ideal which we call `𝓅`.
  obtain ⟨𝓅, h𝓅₁, h𝓅₂⟩ := exists_prime S le_rfl (lt_of_not_ge card)

  have subset_hat : ∀ I : S, ¬ (J : Set R) ⊆ ⋃ (i : S.erase I), i
  · rintro ⟨I, hI⟩ rid
    exact (subset' (S.erase I) (Finset.erase_ssubset hI)) rid
  simp_rw [not_subset] at subset_hat
  -- Since `J` is not a subset of the union of `S`, it is not a subset of the union of `S \ {I}`
  -- for each ideal `I` in `S`. Hence for each `i ∈ S`, we can find an `rᵢ ∈ R` that is in `J` and
  -- `i` but not in the union of `S`.
  choose r hr1 hr2 using subset_hat
  have hr3 : ∀ i, r i ∈ i.1
  · rintro i
    specialize hr2 i
    contrapose! hr2
    specialize subset_union (hr1 i)
    rw [Set.mem_iUnion] at subset_union ⊢
    rcases subset_union with ⟨j, hj⟩
    exact ⟨⟨j.1, Finset.mem_erase.mpr ⟨fun r ↦ hr2 <| r ▸ hj, j.2⟩⟩, hj⟩

  -- Let `a` be `(∏_{i ≠ 𝓅} rᵢ) + r_𝓅`, then `a` is in `J` hence in the union of `S`
  let a := ∏ i in (S.erase 𝓅).attach, r ⟨i.1, erase_subset _ _ i.2⟩ + r ⟨𝓅, h𝓅₁⟩
  have ha1 : a ∈ J
  · obtain ⟨c, hc⟩ : (S.erase 𝓅).Nonempty
    · rw [← Finset.card_pos, Finset.card_erase_eq_ite, if_pos h𝓅₁]
      exact tsub_pos_iff_lt.mpr <| one_lt_two.trans <| not_le.mp card
    exact J.add_mem (Ideal.prod_mem_of_mem _ (mem_attach _ ⟨_, hc⟩) (hr1 _)) (hr1 _)

  specialize subset_union ha1
  rw [mem_iUnion] at subset_union
  -- So there is some `Q ∈ S` such that `a ∈ Q`. We consider two cases `𝓅 = Q` and `𝓅 ≠ Q`.
  obtain ⟨⟨Q, hQ₁⟩, hQ₂⟩ := subset_union
  by_cases H : 𝓅 = Q
  · subst H
    -- If `𝓅 = Q`, then for some `i ≠ 𝓅`, `rᵢ ∈ 𝓅`, this is a contradiction because `rᵢ` is not in
    -- the union of `S \ {i}`.
    obtain ⟨⟨i, hi1⟩, hi2⟩ : ∃ i : S.erase 𝓅, r ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ 𝓅
    · have := 𝓅.sub_mem hQ₂ (hr3 ⟨𝓅, h𝓅₁⟩)
      simp only [add_sub_cancel] at this
      simpa only [Ideal.IsPrime.prod_mem_iff_exists_mem, mem_attach, true_and_iff] using this
    rw [Finset.mem_erase] at hi1
    exact (hr2 ⟨i, hi1.2⟩ <| mem_iUnion.mpr ⟨⟨𝓅, mem_erase.mpr ⟨hi1.1.symm, hQ₁⟩⟩, hi2⟩).elim
  · -- If `𝓅 ≠ Q`, then `∏_{i ≠ 𝓅} xᵢ ∈ 𝓆` and `x_𝓅 ∈ Q` as well (since `a` ∈ `Q`).
    -- This contradicts that `x_𝓅` is not in the union of `S \ {Q}`.
    have mem1 : ∏ i in (S.erase 𝓅).attach, r ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ Q
    · exact Q.prod_mem_of_mem (mem_attach _ ⟨Q, mem_erase.mpr ⟨Ne.symm H, hQ₁⟩⟩) (hr3 ⟨Q, hQ₁⟩)
    have mem2 : r ⟨𝓅, h𝓅₁⟩ ∈ Q := by simpa only [add_sub_cancel'] using Q.sub_mem hQ₂ mem1
    specialize hr2 ⟨𝓅, h𝓅₁⟩
    rw [mem_iUnion] at hr2
    push_neg at hr2
    exact (hr2 ⟨Q, mem_erase.mpr ⟨Ne.symm H, hQ₁⟩⟩ mem2).elim

/--
**Prime Avoidance Lemma** [00DS](https://stacks.math.columbia.edu/tag/00DS)

Let `R` be a commutative ring, `J` an ideal of `R`, `S` be a finite collection of ideals of `R`
such that ideals in `S` are prime ideals except for perhaps at most two.

If `J` is not a subset of any of ideal in `S`, then there is an `x ∈ R` such that `x ∈ J` but `x` is
not in any of the ideals in `S`.
-/
lemma Ideal.exists_mem_and_forall_not_mem_of_not_subset_and_at_most_two_non_primes
    (J : Ideal R)
    (S : Finset (Ideal R))
    (exists_prime : ∀ s ≤ S, 2 < s.card → ∃ p ∈ s, p.IsPrime)
    (not_subset : ∀ I : Ideal R, I ∈ S → ¬ J ≤ I) :
    ∃ r : R, r ∈ J ∧ (∀ I : Ideal R, I ∈ S → r ∉ I) := by
  contrapose! not_subset
  exact J.le_of_subset_union_with_at_most_two_non_primes S exists_prime
    (fun x hx ↦ mem_iUnion.mpr <| let ⟨i, hi1, hi2⟩ := not_subset x hx; ⟨⟨i, hi1⟩, hi2⟩)
