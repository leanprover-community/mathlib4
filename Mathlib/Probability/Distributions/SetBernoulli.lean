/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Probability.Independence.InfinitePi

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
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i : ι} {p : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
noncomputable def setBernoulli : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦ Ber(i ∈ u, False, p)

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

instance : IsProbabilityMeasure setBer(u, p) :=
  MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P ↦ ⟨{i | P i}, rfl⟩

variable (u p) in
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
      (infinitePi fun i : ι ↦ Ber(i ∈ u, False, p)) :=
  MeasurableEquiv.setOfPred.comap_symm

lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ Ber(i ∈ u, False, p)) ((fun t i ↦ i ∈ t) '' S) :=
  MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply ..

lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ Ber(i ∈ u, False, p)) ((fun p ↦ {i | p i}) ⁻¹' S) :=
  MeasurableEquiv.setOfPred.symm.comap_apply ..

variable (u) in
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

variable (u) in
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

lemma setBernoulli_mem_of_mem (p : I) (hi : i ∈ u) :
    setBer(u, p) {s | i ∈ s} = toNNReal p := by
  rw [setBernoulli_eq_map]
  have h1 : {s : Set ι | i ∈ s} = (i ∈ ·) ⁻¹' {True} := by grind
  have h2 : (fun x ↦ i ∈ x) ∘ (fun (p : ι → Prop) ↦ {j | p j}) = (fun x ↦ x i) := by grind
  rw [h1, ← map_apply, map_map, h2, infinitePi_map_eval (fun j ↦ Ber(j ∈ u, False, p))]
  · simp [hi]
  any_goals fun_prop
  simp

lemma setBernoulli_real_mem_of_mem (p : I) (hi : i ∈ u) :
    setBer(u, p).real {s | i ∈ s} = p := by
  simp [measureReal_def, setBernoulli_mem_of_mem p hi]

lemma setBernoulli_mem_of_notMem (p : I) (hi : i ∉ u) :
    setBer(u, p) {s | i ∈ s} = 0 := by
  rw [setBernoulli_eq_map]
  have h1 : {s : Set ι | i ∈ s} = (i ∈ ·) ⁻¹' {True} := by grind
  have h2 : (fun x ↦ i ∈ x) ∘ (fun (p : ι → Prop) ↦ {j | p j}) = (fun x ↦ x i) := by grind
  rw [h1, ← map_apply, map_map, h2, infinitePi_map_eval (fun j ↦ Ber(j ∈ u, False, p))]
  · simp [hi]
  any_goals fun_prop
  simp

lemma setBernoulli_real_mem_of_notMem (p : I) (hi : i ∉ u) :
    setBer(u, p).real {s | i ∈ s} = 0 := by
  simp [measureReal_def, setBernoulli_mem_of_notMem p hi]

lemma HasLaw.indicator_of_setBernoulli_of_mem (hi : i ∈ u) {S : Ω → Set ι} {M : Type*} [Zero M]
    [MeasurableSpace M] (c : M) (hS : HasLaw S setBer(u, p) P) :
    HasLaw ({ω | i ∈ S ω}.indicator (fun _ ↦ c)) Ber(c, 0, p) P := by
  have := hS.isProbabilityMeasure
  have : p = ⟨P.real {ω | i ∈ S ω}, by simp⟩ := by
    ext
    simp only
    rw [hS.measureReal_eq (p := (i ∈ ·)) (by measurability), ← setBernoulli_real_mem_of_mem _ hi]
  rw [this]
  exact hasLaw_indicator_bernoulliMeasure c
    (hS.aemeasurable.nullMeasurableSet_preimage (s := {t | i ∈ t}) (by measurability))

lemma HasLaw.indicator_one_of_setBernoulli_of_mem (hi : i ∈ u) {S : Ω → Set ι} {M : Type*} [Zero M]
    [One M] [MeasurableSpace M] (hS : HasLaw S setBer(u, p) P) :
    HasLaw ({ω | i ∈ S ω}.indicator (1 : Ω → M)) Ber(1, 0, p) P :=
  hS.indicator_of_setBernoulli_of_mem hi 1

lemma HasLaw.indicator_of_setBernoulli_of_notMem (hi : i ∉ u) {S : Ω → Set ι} {M : Type*} [Zero M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (hS : HasLaw S setBer(u, p) P) (f : Ω → M) :
    HasLaw ({ω | i ∈ S ω}.indicator f) (dirac 0) P := by
  have := hS.isProbabilityMeasure
  rw [hasLaw_dirac_iff]
  have : setBer(u, p) {s | ¬ (i ∉ s)} = 0 := by simp [setBernoulli_mem_of_notMem p hi]
  filter_upwards [hS.ae_iff (by fun_prop) |>.2 this] with ω hω
  grind [Set.indicator]

section Countable
variable [Countable ι]

lemma setBernoulli_ae_subset : ∀ᵐ s ∂setBer(u, p), s ⊆ u := by
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem,
    Set.ofPred_exists, Set.ofPred_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i ∈ u
  · simp [*]
  calc
    setBer(u, p) ({s | i ∈ s} ∩ {s | i ∉ u})
    _ = setBer(u, p) {s | i ∈ s} := by simp [hi]
    _ = infinitePi (fun i ↦ Ber(i ∈ u, False, p)) (cylinder {i} {fun _ ↦ True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]
lemma setBernoulli_singleton_of_not_subset {s : Set ι} (p : I) (hs : ¬ s ⊆ u) :
    setBer(u, p) {s} = 0 :=
  Measure.mono_null (by simpa) setBernoulli_ae_subset

/-- `setBer(u, p)` only gives mass to families of sets contained in `u`. -/
lemma setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) :
    setBer(u, p) S = setBer(u, p) { s ∈ S | s ⊆ u} := by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

lemma map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set ℕ) :
    (setBer(u, p).map Set.ncard) s = setBer(u, p) {t ⊆ u | t.ncard ∈ s} := by
  rw [map_apply (by fun_prop) .of_discrete, setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

variable (p) in
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ℝ≥0∞) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ℝ≥0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator, bernoulliMeasure_def]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞)) := by
      rw [tprod_eq_prod, Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.ofPred_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_ofPred, Set.sdiff_eq_compl_inter, Set.inter_comm]

@[simp]
lemma setBernoulli_real_singleton (p : I) (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (1 - p : ℝ) ^ (u \ s).ncard := by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]

lemma map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard).real {k} =
      (u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k) := by
  have : {s ⊆ u | s.ncard ∈ ({k} : Set ℕ)}.Finite := hu.finite_subsets.subset (by grind)
  rw [measureReal_def, map_ncard_setBernoulli_apply, ← measureReal_def,
    ← Set.biUnion_of_singleton (Set.ofPred _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s ∈ this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu, Set.ncard_sdiff' hs.1 hu, hs.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc,
    ← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

lemma map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard) {k} =
      ENNReal.ofReal ((u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k)) := by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp), ← measureReal_def,
    map_ncard_setBernoulli_real_singleton hu]

@[simp]
lemma setBernoulli_empty : setBer((∅ : Set ι), p) = Measure.dirac ∅ := by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ ∈ s
  · have : {t | t ∈ s ∧ t ⊆ ∅} = {∅} := by grind
    simp_all
  · have : {t | t ∈ s ∧ t ⊆ ∅} = ∅ := by grind
    rw [this]
    simp_all

end Countable

@[fun_prop]
lemma _root_.Measurable.inter {α β : Type*} [MeasurableSpace α]
    {f g : α → Set β} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a ↦ f a ∩ g a :=
  .of_eval fun _ ↦ hf.eval.and hg.eval

@[fun_prop]
lemma _root_.AEMeasurable.inter {α β : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g : α → Set β} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a ↦ f a ∩ g a) μ := by
  refine ⟨fun a ↦ hf.mk f a ∩ hg.mk g a, hf.measurable_mk.inter hg.measurable_mk, ?_⟩
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a h1 h2
  simp_all

lemma HasLaw.inter {S : Ω → Set ι} (hS : HasLaw S setBer(s, p) P) :
    HasLaw (fun ω ↦ (S ω) ∩ u) setBer(s ∩ u, p) P where
  map_eq := by
    change map ((· ∩ u) ∘ S) P = _
    have h1 : (fun x ↦ x ∩ u) ∘ (fun p : ι → Prop ↦ {i | p i}) =
        (fun p ↦ {i | p i}) ∘ (fun p i ↦ p i ∧ i ∈ u) := by ext; simp
    rw [← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map,
      setBernoulli_eq_map, map_map, h1, ← map_map,
      infinitePi_map_pi (f := fun i p ↦ p ∧ i ∈ u) (μ := fun i ↦ Ber(i ∈ s, False, p))]
    · congrm map _ (infinitePi fun i ↦ ?_)
      apply eq_bernoulliMeasure <;> simp +contextual
    all_goals fun_prop

lemma indepFun_inter {t : Set ι} {S : Ω → Set ι} (hS : HasLaw S setBer(s, p) P) :
    (S · ∩ t) ⟂ᵢ[P] (S · ∩ u) := by
  have := hS.isProbabilityMeasure
  rw [indepFun_iff_hasLaw_prodMk_prod hS.inter hS.inter]
  refine ⟨by fun_prop, ?_⟩
  change map ((fun s ↦ (s ∩ t, s ∩ u)) ∘ S) P = _
  have h1 : (fun s ↦ (s ∩ t, s ∩ u)) ∘ (fun p : ι → Prop ↦ {i | p i}) =
      ((fun p ↦ ({i | (p i).1}, {i | (p i).2}))) ∘
        (fun p i ↦ (p i ∧ i ∈ t, p i ∧ i ∈ u)) := by ext; simp; grind
  rw [← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map, setBernoulli_eq_map,
    setBernoulli_eq_map, map_map, h1, ← map_map,
    infinitePi_map_pi (f := fun i p ↦ (p ∧ i ∈ t, p ∧ i ∈ u)) (μ := fun i ↦ Ber(i ∈ s, False, p)),
    map_prod_map]
  ·

lemma HasLaw.hasLaw_indicator_infinitePi_ite_of_setBernoulli [DecidablePred (· ∈ u)]
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [Zero M] (c : M)
    {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    HasLaw (fun ω i ↦ {ω' | i ∈ S ω'}.indicator (fun _ ↦ c) ω)
      (infinitePi (fun i ↦ if i ∈ u then Ber(c, 0, p) else dirac 0)) P := by
  classical
  have : (fun ω i ↦ {ω' | i ∈ S ω'}.indicator (fun _ ↦ c) ω) =
      (fun s i ↦ if i ∈ s then c else 0) ∘ S := by ext ω i; by_cases h : i ∈ S ω <;> simp [h]
  rw [this]
  constructor
  · exact Measurable.comp_aemeasurable
      (.of_eval fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))
      hS.aemeasurable
  have : (fun s i ↦ if i ∈ s then c else 0) ∘ (fun (p : ι → Prop) ↦ {i | p i}) =
      fun p i ↦ if p i then c else 0 := by ext; simp
  rw [← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map, map_map, this,
    infinitePi_map_pi (f := fun x q ↦ if q then c else 0) (μ := fun i ↦ Ber(i ∈ u, False, p))]
  · congr with i : 1
    split_ifs with hi <;> simp [hi]
  any_goals fun_prop
  · exact (.of_eval fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))
  · exact Measurable.aemeasurable
      (.of_eval fun i ↦ .ite (by measurability) (by fun_prop) (by fun_prop))

lemma HasLaw.hasLaw_indicator_one_infinitePi_ite_of_setBernoulli [DecidablePred (· ∈ u)]
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [Zero M] [One M]
    {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    HasLaw (fun ω i ↦ {ω' | i ∈ S ω'}.indicator (1 : Ω → M) ω)
      (infinitePi (fun i ↦ if i ∈ u then Ber(1, 0, p) else dirac 0)) P :=
  hS.hasLaw_indicator_infinitePi_ite_of_setBernoulli 1

/-! ### Bernoulli random variables -/

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
