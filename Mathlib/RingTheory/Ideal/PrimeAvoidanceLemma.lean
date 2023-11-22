/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Prime Avoidance Lemma

Let `R` be a commutative ring, `J` an ideal of `R`, `ℐ` be a finite collection of ideals of `R`
such that ideals in `ℐ` are prime ideals except for perhaps at most two.

If `J` is a subset of any of ideal in `ℐ`, then there is an `x ∈ R` such that `x ∈ J` but `x` is
not in any of the ideals in `ℐ`.

## TODO
* graded version
* the version where `R` contains an infinite field.

## Reference
[00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

variable {R : Type _} [CommRing R]
variable [DecidablePred fun I : Ideal R => I.IsPrime]

open BigOperators
open SetLike (coe_subset_coe)
open Finset hiding not_subset
open Set hiding mem_singleton mem_insert

lemma Ideal.le_or_le_of_subset_union (J X Y : Ideal R) (H : (J : Set R) ⊆ X ∪ Y) :
    J ≤ X ∨ J ≤ Y := by
  by_contra rid
  push_neg at rid
  erw [not_subset_iff_exists_mem_not_mem, not_subset_iff_exists_mem_not_mem] at rid
  rcases rid with ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩
  rcases H (J.add_mem hx1 hy1) with h|h
  · refine (H hy1).elim (fun h' => hx2 ?_) (fun h' => hy2 h')
    convert X.sub_mem h h'; aesop
  · refine (H hx1).elim (fun h' => hx2 h') (fun h' => hy2 ?_)
    convert Y.sub_mem h h'; aesop

/--
Let `R` be a commutative ring, `J` an ideal of `R`, `ℐ` be a finite collection of ideals of `R`
such that ideals in `ℐ` are prime ideals except for perhaps at most two.
Then if `J` is a subset of the union of `ℐ`, `J` is already a subset of some ideal `I` in `ℐ`.
-/
theorem Ideal.le_of_subset_union_with_at_most_two_non_primes
    (J : Ideal R)
    (ℐ : Finset (Ideal R))
    (number_of_non_prime : (ℐ.filter fun I => ¬ I.IsPrime).card ≤ 2)
    (subset_union : (J : Set R) ⊆ ⋃ (I : ℐ), I) :
    ∃ I, I ∈ ℐ ∧ J ≤ I := by
  classical
  induction' ℐ using Finset.strongInductionOn with ℐ ih
  by_cases card : ℐ.card ≤ 2
  · replace card : ℐ.card = 0 ∨ ℐ.card = 1 ∨ ℐ.card = 2
    · interval_cases ℐ.card <;> tauto
    obtain card|card|card := card
    · aesop
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp card
      exact ⟨i, mem_singleton_self _, fun x hx ↦ by aesop⟩
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp card
      simp only [mem_singleton, mem_insert, coe_subset_coe, exists_eq_or_imp, exists_eq_left,
        iUnion_subtype, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left] at subset_union ⊢
      exact J.le_or_le_of_subset_union _ _ subset_union

  by_cases subset' : ∀ ℐ', ℐ' ⊂ ℐ → ¬ (J : Set R) ⊆ ⋃ (I : ℐ'), I
  pick_goal 2
  · push_neg at subset'
    obtain ⟨ℐ', lt, le⟩ := subset'
    obtain ⟨I, hI1, hI2⟩ := ih _ lt ((card_le_of_subset <| filter_subset_filter _ lt.1).trans
      number_of_non_prime) le
    exact ⟨I, lt.1 hI1, hI2⟩
  obtain ⟨I, hI⟩ : (ℐ.filter (fun I ↦ I.IsPrime)).Nonempty
  · exact Finset.nonempty_iff_ne_empty.mpr fun h ↦ card <|
      show ℐ.filter (¬ ·.IsPrime) = ℐ by rw [filter_not, h, sdiff_empty] ▸ number_of_non_prime
  rw [mem_filter] at hI
  obtain ⟨hI1, hI2⟩ := hI
  let ℐ_hat : Ideal R → Finset (Ideal R) := ℐ.erase
  have subset_hat : ∀ I : ℐ, ¬ (J : Set R) ⊆ ⋃ (i : ℐ_hat I), i
  · rintro ⟨I, hI⟩ rid
    exact (subset' (ℐ_hat I) (Finset.erase_ssubset hI)) rid
  simp_rw [not_subset] at subset_hat
  choose x hx1 hx2 using subset_hat
  have hx3 : ∀ i, x i ∈ i.1
  · rintro i
    specialize hx2 i
    contrapose! hx2
    specialize subset_union (hx1 i)
    rw [Set.mem_iUnion] at subset_union ⊢
    rcases subset_union with ⟨j, hj⟩
    exact ⟨⟨j.1, Finset.mem_erase.mpr ⟨fun r => hx2 <| r ▸ hj, j.2⟩⟩, hj⟩

  let X := ∏ i in (ℐ.erase I).attach, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ + x ⟨I, hI1⟩
  have hX1 : X ∈ J
  · refine J.add_mem (Ideal.prod_mem_of_mem _ ?_) (hx1 _)
    obtain ⟨c, hc⟩ : (ℐ.erase I).Nonempty
    · rw [← Finset.card_pos, Finset.card_erase_eq_ite, if_pos hI1]
      exact tsub_pos_iff_lt.mpr <| one_lt_two.trans <| not_le.mp card
    exact ⟨⟨c, hc⟩, mem_attach _ _, hx1 _⟩
  specialize subset_union hX1
  rw [mem_iUnion] at subset_union
  obtain ⟨⟨I', hI'₁⟩, hI'₂⟩ := subset_union
  by_cases H : I = I'
  · subst H
    obtain ⟨⟨i, hi1⟩, hi2⟩ : ∃ i : ℐ.erase I, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ I
    · have := I.sub_mem hI'₂ (hx3 ⟨I, hI1⟩)
      simp only [add_sub_cancel] at this
      simpa only [Ideal.IsPrime.prod_mem_iff_exists_mem, mem_attach, true_and_iff] using this
    rw [Finset.mem_erase] at hi1
    exact (hx2 ⟨i, hi1.2⟩ <| mem_iUnion.mpr ⟨⟨I, mem_erase.mpr ⟨hi1.1.symm, hI'₁⟩⟩, hi2⟩).elim
  · have mem1 : ∏ i in (ℐ.erase I).attach, x ⟨i.1, Finset.erase_subset _ _ i.2⟩ ∈ I'
    · exact I'.prod_mem_of_mem ⟨⟨I', mem_erase.mpr ⟨Ne.symm H, hI'₁⟩⟩, mem_attach _ _, hx3 _⟩
    have mem2 : x ⟨I, hI1⟩ ∈ I' := by simpa only [add_sub_cancel'] using I'.sub_mem hI'₂ mem1
    specialize hx2 ⟨I, hI1⟩
    rw [mem_iUnion] at hx2
    push_neg at hx2
    exact (hx2 ⟨I', Finset.mem_erase.mpr ⟨Ne.symm H, hI'₁⟩⟩ mem2).elim

/--
**Prime Avoidance Lemma** [00DS](https://stacks.math.columbia.edu/tag/00DS)

Let `R` be a commutative ring, `J` an ideal of `R`, `ℐ` be a finite collection of ideals of `R`
such that ideals in `ℐ` are prime ideals except for perhaps at most two.

If `J` is a subset of any of ideal in `ℐ`, then there is an `x ∈ R` such that `x ∈ J` but `x` is
not in any of the ideals in `ℐ`.
-/
lemma Ideal.exists_mem_and_forall_not_mem_of_not_subset_and_at_most_two_non_primes
    (J : Ideal R)
    (ℐ : Finset (Ideal R))
    (number_of_non_prime : (ℐ.filter fun I => ¬ I.IsPrime).card ≤ 2)
    (not_subset : ∀ I : Ideal R, I ∈ ℐ → ¬ J ≤ I) :
    ∃ x : R, x ∈ J ∧ (∀ I : Ideal R, I ∈ ℐ → x ∉ I) := by
  contrapose! not_subset
  exact J.le_of_subset_union_with_at_most_two_non_primes ℐ number_of_non_prime
    (fun x hx ↦ mem_iUnion.mpr <| let ⟨i, hi1, hi2⟩ := not_subset x hx; ⟨⟨i, hi1⟩, hi2⟩)
