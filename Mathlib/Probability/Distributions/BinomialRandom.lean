/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Probability.ProductMeasure

/-!
# Binomial random distribution

This file defines the binomial random distribution on a set. For a set `u : Set ι` and `p` between
`0` and `1`, this is the measure on `Set ι` such that each `i ∈ u` belongs to the random set with
probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`Bin(u, p)` is the binomial distribution on `u` with probability `p`.

## TODO

Add the characteristic predicate for a random variable to follow the binomial distribution.
-/

open MeasureTheory Measure unitInterval
open scoped Finset

namespace ProbabilityTheory
variable {ι : Type*} {s u : Set ι} {i : ι} {p : I}

variable (u p) in
/-- The binomial distribution with parameter `p` on the set `u : Set V` is the measure on `Set V`
such that each element of `u` is taken with probability `p`, and the elements outside of `u` are
never taken. -/
noncomputable def binomialRandomOn : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "Bin(" u ", " p ")" => binomialRandomOn u p

instance : IsProbabilityMeasure Bin(u, p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <| .of_forall fun P ↦
    ⟨{a | P a}, rfl⟩

variable (u p) in
lemma binomialRandomOn_eq_map :
    Bin(u, p) = .map (fun p ↦ {i | p i})
      (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOf.comap_symm

lemma binomialRandomOn_apply (S : Set (Set ι)) :
    Bin(u, p) S = (infinitePi fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
      ((fun t a ↦ a ∈ t) '' S) := by
  convert MeasurableEquiv.setOf.symm.measurableEmbedding.comap_apply ..

lemma binomialRandomOn_apply' (S : Set (Set ι)) :
    Bin(u, p) S = (infinitePi fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
      ((fun p ↦ {a | p a}) ⁻¹' S) := by
  convert MeasurableEquiv.setOf.symm.comap_apply ..

variable (u) in
@[simp] lemma binomialRandomOn_zero : Bin(u, 0) = dirac ∅ := by simp [binomialRandomOn_eq_map]

variable (u) in
@[simp] lemma binomialRandomOn_one : Bin(u, 1) = dirac u := by simp [binomialRandomOn_eq_map]

section Countable
variable [Countable ι]

-- TODO: Does this hold if `ι` isn't countable? Note: the current proof only needs `u` cocountable,
-- but we don't bother doing this minigeneralisation.
lemma binomialRandomOn_ae_subset : ∀ᵐ s ∂Bin(u, p), s ⊆ u := by
  classical
  change _ = _
  simp only [Set.compl_setOf, Set.not_subset_iff_exists_mem_notMem, Set.setOf_exists, Set.setOf_and,
    measure_iUnion_null_iff]
  rintro a
  by_cases ha : a ∈ u
  · simp [*]
  calc
    Bin(u, p) ({s | a ∈ s} ∩ {s | a ∉ u})
    _ = Bin(u, p) {s | a ∈ s} := by simp [ha]
    _ = infinitePi (fun a ↦ toNNReal p • dirac (a ∈ u) + toNNReal (σ p) • dirac False)
            (cylinder {a} {fun _ ↦ True}) := by
      rw [binomialRandomOn_apply']
      congr!
      ext
      simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder _ (.singleton _), ha]

end Countable

variable (u p) in
-- TODO: Generalise to countable `ι` and finite `u`. See the TODO on `infinitePi_pi`.
@[simp] lemma binomialRandomOn_singleton [Finite ι] (hsu : s ⊆ u) :
    Bin(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  cases nonempty_fintype ι
  lift u to Finset ι using Set.toFinite _
  calc
    Bin(u, p) {s}
    _ = ∏ i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ENNReal) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ENNReal)) := by
      simp [binomialRandomOn_apply, Set.image_singleton, Set.indicator]
      simp [ENNReal.smul_def]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ENNReal) else (toNNReal (σ p) : ENNReal)) := by
      rw [← Finset.prod_subset u.subset_univ (by
        simpa +contextual [ite_add_ite, ← ENNReal.coe_add] using fun _ ↦ mt (@hsu _))]
      simp +contextual [ite_add_ite]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.setOf_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_setOf, Set.diff_eq_compl_inter, Set.inter_comm]

end ProbabilityTheory
