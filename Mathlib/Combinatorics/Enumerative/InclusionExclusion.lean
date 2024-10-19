/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Ring.NegOnePow

/-!
# Inclusion-exclusion principle

This file proves several variants of the inclusion-exclusion principle.

## TODO

Use `Finset.prod_indicator_biUnion_sub_indicator` to prove the integral version of
inclusion-exclusion.
-/

open Int

namespace Finset
variable {ι α G : Type*} [DecidableEq α] [AddCommGroup G] {s : Finset ι}

lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (f : ι → Finset α) (a : α) :
    ∏ i ∈ s, (Set.indicator (s.biUnion f) 1 a - Set.indicator (f i) 1 a) = (0 : ℤ) := by
  by_cases ha : a ∈ s.biUnion f
  · obtain ⟨i, hi, ha⟩ := mem_biUnion.1 ha
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ f i := fun h ↦ ha <| subset_biUnion_of_mem _ hi h
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]

/-- **Inclusion-exclusion principle** for the sum of a function over a union.

The sum of a function `g` over the union of the `f i` over `i ∈ s` is the alternating sum of the
sums of `g` over the intersections of the `f i`. -/
theorem inclusion_exclusion_sum_biUnion (s : Finset ι) (f : ι → Finset α) (g : α → G) :
    ∑ a ∈ s.biUnion f, g a = ∑ t : s.powerset.filter (·.Nonempty),
      negOnePow (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 f, g a := by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a ∈ s.biUnion f, g a - ∑ t : s.powerset.filter (·.Nonempty),
      negOnePow (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 f, g a
      = ∑ t : s.powerset.filter (·.Nonempty),
          negOnePow #t.1 • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 f, g a +
          ∑ t ∈ s.powerset.filter (¬ ·.Nonempty), negOnePow #t • ∑ a ∈ s.biUnion f, g a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', negOnePow_succ]
    _ = ∑ t ∈ s.powerset, negOnePow #t •
          if ht : t.Nonempty then ∑ a ∈ t.inf' ht f, g a else ∑ a ∈ s.biUnion f, g a := by
      rw [← sum_attach (filter ..)]; simp [sum_dite, filter_eq', sum_attach]
    _ = ∑ a ∈ s.biUnion f, (∏ i ∈ s, (1 - Set.indicator (f i) 1 a : ℤ)) • g a := by
      simp only [Int.reduceNeg, mem_coe, prod_sub, sum_comm (s := s.biUnion f), sum_smul, mul_assoc]
      congr! with t
      split_ifs with ht
      · obtain ⟨i, hi⟩ := ht
        simp only [prod_const_one, mul_one, prod_indicator_apply]
        simp only [smul_sum, Units.smul_def, coe_negOnePow_natCast, reduceNeg, Set.indicator,
          inf_set_eq_iInter, Set.mem_iInter, mem_coe, Pi.one_apply, mul_ite, mul_one, mul_zero,
          ite_smul, zero_smul, sum_ite, not_forall, sum_const_zero, add_zero]
        congr!
        aesop
      · obtain rfl := not_nonempty_iff_eq_empty.1 ht
        simp
    _ = ∑ a ∈ s.biUnion f, (∏ i ∈ s,
          (Set.indicator (s.biUnion f) 1 a - Set.indicator (f i) 1 a) : ℤ) • g a := by
      congr! with t; rw [Set.indicator_of_mem ‹_›, Pi.one_apply]
    _ = 0 := by
      obtain rfl | hs := s.eq_empty_or_nonempty <;>
        simp [-coe_biUnion, prod_indicator_biUnion_sub_indicator, *]

/-- **Inclusion-exclusion principle** for the cardinality of a union.

The cardinality of the union of the `f i` over `i ∈ s` is the alternating sum of the cardinalities
of the intersections of the `f i`. -/
theorem inclusion_exclusion_card_biUnion (s : Finset ι) (f : ι → Finset α) :
    #(s.biUnion f) = ∑ t : s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t.1 + 1) * #(t.1.inf' (mem_filter.1 t.2).2 f) := by
  simpa using inclusion_exclusion_sum_biUnion (G := ℤ) s f (g := 1)

variable [Fintype α]

/-- **Inclusion-exclusion principle** for the sum of a function over an intersection of complements.

The sum of a function `g` over the intersection of the complements of the `f i` over `i ∈ s` is the
alternating sum of the sums of `g` over the intersections of the `f i`. -/
theorem inclusion_exclusion_sum_inf_compl (s : Finset ι) (f : ι → Finset α) (g : α → G) :
    ∑ a ∈ s.inf fun i ↦ (f i)ᶜ, g a = ∑ t ∈ s.powerset, negOnePow #t • ∑ a ∈ t.inf f, g a := by
  classical
  calc
    ∑ a ∈ s.inf fun i ↦ (f i)ᶜ, g a
      = ∑ a, g a - ∑ a ∈ s.biUnion f, g a := by
      rw [← Finset.compl_sup, sup_eq_biUnion, eq_sub_iff_add_eq, sum_compl_add_sum]
    _ = ∑ t ∈ s.powerset.filter (¬ ·.Nonempty), negOnePow #t • ∑ a ∈ t.inf f, g a
          + ∑ t ∈ s.powerset.filter (·.Nonempty), negOnePow #t • ∑ a ∈ t.inf f, g a := by
      simp [← sum_attach (filter ..), inclusion_exclusion_sum_biUnion, inf'_eq_inf, filter_eq',
        sub_eq_add_neg, negOnePow_succ]
    _ = ∑ t ∈ s.powerset, negOnePow #t • ∑ a ∈ t.inf f, g a := sum_filter_not_add_sum_filter ..

/-- **Inclusion-exclusion principle** for the cardinality of an intersection of complements.

The cardinality of the intersection of the complements of the `f i` over `i ∈ s` is the
alternating sum of the cardinalities of the intersections of the `f i`. -/
theorem inclusion_exclusion_card_inf_compl (s : Finset ι) (f : ι → Finset α) :
    #(s.inf fun i ↦ (f i)ᶜ) = ∑ t ∈ s.powerset, (-1 : ℤ) ^ #t * #(t.inf f) := by
  simpa using inclusion_exclusion_sum_inf_compl (G := ℤ) s f (g := 1)

end Finset
