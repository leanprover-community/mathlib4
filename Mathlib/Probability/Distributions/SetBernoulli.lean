/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLawExists

/-!
# Product of bernoulli distributions on a set

This file defines the product of bernoulli distributions on a set as a measure on sets.
For a set `u : Set ι` and `p` between `0` and `1`, this is the measure on `Set ι` such that each
`i ∈ u` belongs to the random set with probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`setBer(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

It is painful to convert from `unitInterval` to `ENNReal`. Should we introduce a coercion or
explicit operation (like `unitInterval.toNNReal`, note the lack of dot notation!)?
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
noncomputable def setBernoulli : Measure (Set ι) :=
  independentSetMeasure (fun i ↦ bernoulliMeasure (i ∈ u) False p)

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

variable (u p) in
theorem setBernoulli_def :
  setBer(u, p) = independentSetMeasure (fun i ↦ bernoulliMeasure (i ∈ u) False p) := rfl

instance : IsProbabilityMeasure setBer(u, p) := by rw [setBernoulli_def]; infer_instance

variable (u p) in
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
    (infinitePi fun i ↦ bernoulliMeasure (i ∈ u) False p) :=
  MeasurableEquiv.setOf.comap_symm

variable (u p) in
lemma setBernoulli_eq_independent_set_measure_ite [∀ i, Decidable (i ∈ u)] :
    setBer(u, p) = independentSetMeasure
      (fun i ↦ if i ∈ u then bernoulliMeasure True False p else dirac false) := by
  rw [setBernoulli_def]
  congr
  ext i s hs
  by_cases hi : i ∈ u <;> simp [hi]

set_option backward.isDefEq.respectTransparency false in
variable (u) in
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by
  simp [setBernoulli_eq_map, bernoulli_measure_def]

set_option backward.isDefEq.respectTransparency false in
variable (u) in
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by
  simp [setBernoulli_eq_map, bernoulli_measure_def]

section Countable
variable [Countable ι]

variable (u p) in
theorem hasLaw_setBernoulli_of_bernoulli_iid [IsProbabilityMeasure P] (B : ι → Ω → Prop)
    (hU : ∀ i, HasLaw (B i) (bernoulliMeasure True False p) P) (hU' : iIndepFun B P) :
    HasLaw ({i ∈ u | B i ·}) (setBer(u, p)) P where
  map_eq := by
    simp_rw [← Function.comp_def (f := fun B ↦ {i ∈ u | B i}) (g := fun ω : Ω ↦ (B · ω)),
      ← Function.comp_def (f := fun p ↦ {i | p i}) (g := fun (p : ι → Prop) i ↦ i ∈ u ∧ p i)]
    rw [← AEMeasurable.map_map_of_aemeasurable (Measurable.aemeasurable <| by fun_prop)
      (by fun_prop), ← map_map (by fun_prop) (by fun_prop),
      (iIndepFun_iff_map_fun_eq_infinitePi_map₀ (by fun_prop)).mp hU']
    simp_rw [(hU _).map_eq]
    rw [infinitePi_map_pi _ (by fun_prop)]
    simp [setBernoulli_eq_map]

theorem hasLaw_setBernoulli_of_uniform_iid [IsProbabilityMeasure P] (p : I) (U : ι → Ω → I)
    (hU : ∀ i, HasLaw (U i) ℙ P) (hU' : iIndepFun U P) :
    HasLaw ({i ∈ u | U i · ≤ p}) (setBer(u, p)) P where
  map_eq := by
    refine hasLaw_setBernoulli_of_bernoulli_iid u p (fun i ω ↦ U i ω ≤ p) ?_ ?_ |>.map_eq
    · intro i
      exact (hU i).uniform_le_hasLaw p
    · change iIndepFun (fun i ↦ (· ≤ p) ∘ (U i)) P
      apply hU'.comp
      fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma setBernoulli_ae_subset : ∀ᵐ s ∂setBer(u, p), s ⊆ u := by
  obtain ⟨_, _, _, B, _, hB_law, hB_indep, _⟩ := exists_iid ι (bernoulliMeasure True False p)
  rw [← (hasLaw_setBernoulli_of_bernoulli_iid u p B hB_law hB_indep).map_eq,
    ae_map_iff (by fun_prop) (by measurability)]
  filter_upwards with ω using by grind

set_option backward.isDefEq.respectTransparency false in
variable (u p) in
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = ENNReal.ofReal p ^ s.ncard * ENNReal.ofReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏ i ∈ u, (if i ∈ s then ENNReal.ofReal p else ENNReal.ofReal (σ p)) := by
      rw [setBernoulli_eq_independent_set_measure_ite, independent_set_measure_apply,
        Set.image_singleton, infinitePi_singleton, tprod_eq_prod, Finset.prod_congr rfl]
      · simp +contextual [bernoulli_measure_def, ite_add_ite, Pi.single, Function.update]
      · simp +contextual [mt (@hsu _)]
    _ = ENNReal.ofReal p ^ s.ncard * ENNReal.ofReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.setOf_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_setOf, Set.diff_eq_compl_inter, Set.inter_comm]

variable (u p) in
@[simp] lemma setBernoulli_real_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (σ p) ^ (u \ s).ncard := by
  simp (disch := unit_interval) [measureReal_def, setBernoulli_singleton u p hsu hu]

theorem continuous_setBernoulli (hu : u.Finite) {S : Set (Set ι)} (hS : ∀ s ∈ S, s ⊆ u) :
    Continuous fun p ↦ setBer(u,p).real S := by
  classical
  lift S to Finset (Set ι) using hu.finite_subsets.subset hS
  conv in setBer(u, _).real _ =>
    rw [measureReal_def, ← sum_measure_singleton, ENNReal.toReal_sum (by simp)]
  apply continuous_finset_sum
  intro s hsS
  simp_rw [← measureReal_def, setBernoulli_real_singleton u _ (hS s hsS) hu]
  fun_prop

theorem setBernoulli_image (hu : u.Finite) (S : Set (Set ι)) (hS : ∀ s ∈ S, s ⊆ u)
    (hSu : u ∈ S) (hSempty : ∅ ∉ S) : (fun p ↦ setBer(u, p).real S) '' Set.univ = I := by
  classical
  lift S to Finset (Set ι) using hu.finite_subsets.subset hS
  apply Set.Subset.antisymm
  · rintro q ⟨p, h, rfl⟩
    simp [measureReal_le_one]
  · convert intermediate_value_Icc (a := (0 : I)) (b := (1 : I)) (f := fun p ↦ setBer(u,p).real S)
      (by simp) (continuous_setBernoulli hu hS |>.continuousOn)
    · simp [measureReal_def, hSempty]
    · simp [measureReal_def, hSu]
    · exact (Set.eq_univ_of_forall (fun ⟨q, hq⟩ ↦ by simpa [Subtype.mk_le_mk] using hq.2)).symm

section UpperSet

theorem monotone_setBernoulli {S : Set (Set ι)} (hS_meas : MeasurableSet S)
    (hS : IsRelUpperSet S (· ⊆ u)) : Monotone fun p ↦ setBer(u, p) S := by
  intro p q hpq
  obtain ⟨_, _, _, U, _, hU_law, hU_indep, _⟩ := exists_iid ι (ℙ : Measure I)
  simp only [IsRelUpperSet, Set.le_eq_subset,
    ← (hasLaw_setBernoulli_of_uniform_iid p U hU_law hU_indep).map_eq,
    ← (hasLaw_setBernoulli_of_uniform_iid q U hU_law hU_indep).map_eq] at hS ⊢
  repeat rw [map_apply (by fun_prop) (by measurability)]
  exact measure_mono (fun ω h ↦ (hS h).2 (by grind) (by grind))

end UpperSet

end Countable

/-! ### SetBernoulli random variables -/

variable (X u p P) in
/-- A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its distribution is
the product over `u` of `p`-bernoulli distributions. -/
abbrev IsSetBernoulli : Prop := HasLaw X setBer(u, p) P

lemma isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P :=
  hasLaw_congr hXY

variable [Countable ι]

lemma IsSetBernoulli.ae_subset (hX : IsSetBernoulli X u p P) : ∀ᵐ ω ∂P, X ω ⊆ u :=
  (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

end ProbabilityTheory
