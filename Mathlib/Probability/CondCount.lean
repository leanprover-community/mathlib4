/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Count

#align_import probability.cond_count from "leanprover-community/mathlib"@"117e93f82b5f959f8193857370109935291f0cc4"

/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occurring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the probability over
the entire sample space when `s = Set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `ProbabilityTheory.condCount`: given a set `s`, `condCount s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allow us to describe this by abusing the definitional equality of sets and predicates by simply
writing `condCount s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/


noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Given a set `s`, `condCount s` is the counting measure conditioned on `s`. In particular,
`condCount s t` is the proportion of `s` that is contained in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`ProbabilityTheory.condCount_isProbabilityMeasure`. -/
def condCount (s : Set Ω) : Measure Ω :=
  Measure.count[|s]
#align probability_theory.cond_count ProbabilityTheory.condCount

@[simp]
theorem condCount_empty_meas : (condCount ∅ : Measure Ω) = 0 := by simp [condCount]
                                                                   -- 🎉 no goals
#align probability_theory.cond_count_empty_meas ProbabilityTheory.condCount_empty_meas

theorem condCount_empty {s : Set Ω} : condCount s ∅ = 0 := by simp
                                                              -- 🎉 no goals
#align probability_theory.cond_count_empty ProbabilityTheory.condCount_empty

theorem finite_of_condCount_ne_zero {s t : Set Ω} (h : condCount s t ≠ 0) : s.Finite := by
  by_contra hs'
  -- ⊢ False
  simp [condCount, cond, Measure.count_apply_infinite hs'] at h
  -- 🎉 no goals
#align probability_theory.finite_of_cond_count_ne_zero ProbabilityTheory.finite_of_condCount_ne_zero

theorem condCount_univ [Fintype Ω] {s : Set Ω} :
    condCount Set.univ s = Measure.count s / Fintype.card Ω := by
  rw [condCount, cond_apply _ MeasurableSet.univ, ← ENNReal.div_eq_inv_mul, Set.univ_inter]
  -- ⊢ ↑↑Measure.count s / ↑↑Measure.count Set.univ = ↑↑Measure.count s / ↑(Fintype …
  congr
  -- ⊢ ↑↑Measure.count Set.univ = ↑(Fintype.card Ω)
  rw [← Finset.coe_univ, Measure.count_apply, Finset.univ.tsum_subtype' fun _ => (1 : ENNReal)]
  -- ⊢ (Finset.sum Finset.univ fun x => 1) = ↑(Fintype.card Ω)
  · simp [Finset.card_univ]
    -- 🎉 no goals
  · exact (@Finset.coe_univ Ω _).symm ▸ MeasurableSet.univ
    -- 🎉 no goals
#align probability_theory.cond_count_univ ProbabilityTheory.condCount_univ

variable [MeasurableSingletonClass Ω]

theorem condCount_isProbabilityMeasure {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (condCount s) :=
  { measure_univ := by
      rw [condCount, cond_apply _ hs.measurableSet, Set.inter_univ, ENNReal.inv_mul_cancel]
      -- ⊢ ↑↑Measure.count s ≠ 0
      · exact fun h => hs'.ne_empty <| Measure.empty_of_count_eq_zero h
        -- 🎉 no goals
      · exact (Measure.count_apply_lt_top.2 hs).ne }
        -- 🎉 no goals
#align probability_theory.cond_count_is_probability_measure ProbabilityTheory.condCount_isProbabilityMeasure

theorem condCount_singleton (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)] :
    condCount {ω} t = if ω ∈ t then 1 else 0 := by
  rw [condCount, cond_apply _ (measurableSet_singleton ω), Measure.count_singleton, inv_one,
    one_mul]
  split_ifs
  -- ⊢ ↑↑Measure.count ({ω} ∩ t) = 1
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = {ω}), Measure.count_singleton]
    -- 🎉 no goals
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = ∅), Measure.count_empty]
    -- 🎉 no goals
#align probability_theory.cond_count_singleton ProbabilityTheory.condCount_singleton

variable {s t u : Set Ω}

theorem condCount_inter_self (hs : s.Finite) : condCount s (s ∩ t) = condCount s t := by
  rw [condCount, cond_inter_self _ hs.measurableSet]
  -- 🎉 no goals
#align probability_theory.cond_count_inter_self ProbabilityTheory.condCount_inter_self

theorem condCount_self (hs : s.Finite) (hs' : s.Nonempty) : condCount s s = 1 := by
  rw [condCount, cond_apply _ hs.measurableSet, Set.inter_self, ENNReal.inv_mul_cancel]
  -- ⊢ ↑↑Measure.count s ≠ 0
  · exact fun h => hs'.ne_empty <| Measure.empty_of_count_eq_zero h
    -- 🎉 no goals
  · exact (Measure.count_apply_lt_top.2 hs).ne
    -- 🎉 no goals
#align probability_theory.cond_count_self ProbabilityTheory.condCount_self

theorem condCount_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s ⊆ t) :
    condCount s t = 1 := by
  haveI := condCount_isProbabilityMeasure hs hs'
  -- ⊢ ↑↑(condCount s) t = 1
  refine' eq_of_le_of_not_lt prob_le_one _
  -- ⊢ ¬↑↑(condCount s) t < 1
  rw [not_lt, ← condCount_self hs hs']
  -- ⊢ ↑↑(condCount s) s ≤ ↑↑(condCount s) t
  exact measure_mono ht
  -- 🎉 no goals
#align probability_theory.cond_count_eq_one_of ProbabilityTheory.condCount_eq_one_of

theorem pred_true_of_condCount_eq_one (h : condCount s t = 1) : s ⊆ t := by
  have hsf := finite_of_condCount_ne_zero (by rw [h]; exact one_ne_zero)
  -- ⊢ s ⊆ t
  rw [condCount, cond_apply _ hsf.measurableSet, mul_comm] at h
  -- ⊢ s ⊆ t
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  -- ⊢ s ⊆ t
  rw [inv_inv, Measure.count_apply_finite _ hsf, Measure.count_apply_finite _ (hsf.inter_of_left _),
    Nat.cast_inj] at h
  suffices s ∩ t = s by exact this ▸ fun x hx => hx.2
  -- ⊢ s ∩ t = s
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  -- ⊢ Set.Finite.toFinset (_ : Set.Finite (s ∩ t)) = Set.Finite.toFinset hsf
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono <| s.inter_subset_left t) h.ge
  -- 🎉 no goals
#align probability_theory.pred_true_of_cond_count_eq_one ProbabilityTheory.pred_true_of_condCount_eq_one

theorem condCount_eq_zero_iff (hs : s.Finite) : condCount s t = 0 ↔ s ∩ t = ∅ := by
  simp [condCount, cond_apply _ hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]
#align probability_theory.cond_count_eq_zero_iff ProbabilityTheory.condCount_eq_zero_iff

theorem condCount_of_univ (hs : s.Finite) (hs' : s.Nonempty) : condCount s Set.univ = 1 :=
  condCount_eq_one_of hs hs' s.subset_univ
#align probability_theory.cond_count_of_univ ProbabilityTheory.condCount_of_univ

theorem condCount_inter (hs : s.Finite) :
    condCount s (t ∩ u) = condCount (s ∩ t) u * condCount s t := by
  by_cases hst : s ∩ t = ∅
  -- ⊢ ↑↑(condCount s) (t ∩ u) = ↑↑(condCount (s ∩ t)) u * ↑↑(condCount s) t
  · rw [hst, condCount_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      condCount_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [condCount, condCount, cond_apply _ hs.measurableSet, cond_apply _ hs.measurableSet,
    cond_apply _ (hs.inter_of_left _).measurableSet, mul_comm _ (Measure.count (s ∩ t)),
    ← mul_assoc, mul_comm _ (Measure.count (s ∩ t)), ← mul_assoc, ENNReal.mul_inv_cancel, one_mul,
    mul_comm, Set.inter_assoc]
  · rwa [← Measure.count_eq_zero_iff] at hst
    -- 🎉 no goals
  · exact (Measure.count_apply_lt_top.2 <| hs.inter_of_left _).ne
    -- 🎉 no goals
#align probability_theory.cond_count_inter ProbabilityTheory.condCount_inter

theorem condCount_inter' (hs : s.Finite) :
    condCount s (t ∩ u) = condCount (s ∩ u) t * condCount s u := by
  rw [← Set.inter_comm]
  -- ⊢ ↑↑(condCount s) (u ∩ t) = ↑↑(condCount (s ∩ u)) t * ↑↑(condCount s) u
  exact condCount_inter hs
  -- 🎉 no goals
#align probability_theory.cond_count_inter' ProbabilityTheory.condCount_inter'

theorem condCount_union (hs : s.Finite) (htu : Disjoint t u) :
    condCount s (t ∪ u) = condCount s t + condCount s u := by
  rw [condCount, cond_apply _ hs.measurableSet, cond_apply _ hs.measurableSet,
    cond_apply _ hs.measurableSet, Set.inter_union_distrib_left, measure_union, mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]
  -- 🎉 no goals
#align probability_theory.cond_count_union ProbabilityTheory.condCount_union

theorem condCount_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) :
    condCount s t + condCount s tᶜ = 1 := by
  rw [← condCount_union hs disjoint_compl_right, Set.union_compl_self,
    (condCount_isProbabilityMeasure hs hs').measure_univ]
#align probability_theory.cond_count_compl ProbabilityTheory.condCount_compl

theorem condCount_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    condCount s u * condCount (s ∪ t) s + condCount t u * condCount (s ∪ t) t =
      condCount (s ∪ t) u := by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  -- ⊢ ↑↑(condCount ∅) u * ↑↑(condCount (∅ ∪ t)) ∅ + ↑↑(condCount t) u * ↑↑(condCou …
                                                     -- ⊢ ↑↑(condCount ∅) u * ↑↑(condCount (∅ ∪ ∅)) ∅ + ↑↑(condCount ∅) u * ↑↑(condCou …
                                                     -- ⊢ ↑↑(condCount s) u * ↑↑(condCount (s ∪ ∅)) s + ↑↑(condCount ∅) u * ↑↑(condCou …
  · simp
    -- 🎉 no goals
  · simp [condCount_self ht ht']
    -- 🎉 no goals
  · simp [condCount_self hs hs']
    -- 🎉 no goals
  rw [condCount, condCount, condCount, cond_apply _ hs.measurableSet,
    cond_apply _ ht.measurableSet, cond_apply _ (hs.union ht).measurableSet,
    cond_apply _ (hs.union ht).measurableSet, cond_apply _ (hs.union ht).measurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right,
      mul_comm (Measure.count (s ∪ t))⁻¹, mul_comm (Measure.count (s ∪ t))⁻¹, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Measure.count s), mul_comm _ (Measure.count t), ← mul_assoc,
      ← mul_assoc]
  rw [ENNReal.mul_inv_cancel, ENNReal.mul_inv_cancel, one_mul, one_mul, ← add_mul, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts [hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).measurableSet,
    Measure.count_ne_zero ht', (Measure.count_apply_lt_top.2 ht).ne, Measure.count_ne_zero hs',
    (Measure.count_apply_lt_top.2 hs).ne]
#align probability_theory.cond_count_disjoint_union ProbabilityTheory.condCount_disjoint_union

/-- A version of the law of total probability for counting probabilities. -/
theorem condCount_add_compl_eq (u t : Set Ω) (hs : s.Finite) :
    condCount (s ∩ u) t * condCount s u + condCount (s ∩ uᶜ) t * condCount s uᶜ =
      condCount s t := by
  -- Porting note: The original proof used `conv_rhs`. However, that tactic timed out.
  have : condCount s t = (condCount (s ∩ u) t * condCount (s ∩ u ∪ s ∩ uᶜ) (s ∩ u) +
      condCount (s ∩ uᶜ) t * condCount (s ∩ u ∪ s ∩ uᶜ) (s ∩ uᶜ)) := by
    rw [condCount_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right), Set.inter_union_compl]
  rw [this]
  -- ⊢ ↑↑(condCount (s ∩ u)) t * ↑↑(condCount s) u + ↑↑(condCount (s ∩ uᶜ)) t * ↑↑( …
  simp [condCount_inter_self hs]
  -- 🎉 no goals
#align probability_theory.cond_count_add_compl_eq ProbabilityTheory.condCount_add_compl_eq

end ProbabilityTheory
