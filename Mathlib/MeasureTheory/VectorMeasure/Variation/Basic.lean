/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset Set
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]
  {μ ν : VectorMeasure X V} {s : Set X}

lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `sum_le_preVariationFun_of_subset`. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : ∀ t ∈ Q'.parts, t ⊆ s := by simp [Q', Q]; grind
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
      exact hs.diff <| .biUnion (Finset.countable_toSet _) (by simp)

/-- Measure version of `preVariation.exists_Finpartition_sum_gt`. -/
lemma exists_lt_sum_of_lt_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.variation s) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ a < ∑ p ∈ P, ‖μ p‖ₑ := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at ha ⊢
  obtain ⟨P, hP⟩ : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      a < ∑ p ∈ P.parts, (fun x ↦ ‖μ x‖ₑ) p :=
    preVariation.exists_Finpartition_sum_gt (‖μ ·‖ₑ) _ ha
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi  j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht ↦ hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/-- Measure version of `preVariation.exists_Finpartition_sum_ge'`. -/
lemma exists_variation_le_add' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hμ : μ.variation s ≠ ∞) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at hμ ⊢
  obtain ⟨P, hP⟩ : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      preVariationFun (fun x ↦ ‖μ x‖ₑ) s ≤ ∑ p ∈ P.parts, (fun x ↦ ‖μ x‖ₑ) ↑p + ε :=
    preVariation.exists_Finpartition_sum_ge' (‖μ ·‖ₑ) hs hε hμ
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi  j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht ↦ hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/-- Measure version of `preVariation.exists_Finpartition_sum_ge`. -/
lemma exists_variation_le_add (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0} (hε : 0 < ε) (hμ : μ.variation s ≠ ∞) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε :=
  exists_variation_le_add' μ hs (mod_cast hε) hμ

theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [μ.not_measurable' hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

lemma variation_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s)
    (h : ∀ E, MeasurableSet E → E ⊆ s → ‖μ E‖ₑ ≤ m E) :
    μ.variation s ≤ m s := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x ∈ i.parts, ‖μ x‖ₑ ≤ ∑ x ∈ i.parts, m x := Finset.sum_le_sum
        (fun s hs => h s s.property (i.le hs))
    _ = m (i.parts.sup Subtype.val) := by
      rw [sup_set_eq_biUnion]
      refine (MeasureTheory.measure_biUnion_finset ?_ fun b _ => b.property).symm
      intro a ha b hb hab
      simpa [disjoint_iff, Subtype.ext_iff] using i.disjoint ha hb hab
    _ ≤ m s := by
      rw [sup_set_eq_biUnion]
      exact measure_mono <| Set.iUnion₂_subset fun _ hp => Subtype.coe_le_coe.mpr (i.le hp)

lemma variation_le_of_forall_enorm_le {m : Measure X} (h : ∀ E, MeasurableSet E → ‖μ E‖ₑ ≤ m E) :
    μ.variation ≤ m :=
  Measure.le_intro fun _ hs _ => variation_apply_le_of_forall_enorm_le hs (fun E hE _ ↦ h E hE)

lemma variation_add_le [ContinuousAdd V] : variation (μ + ν) ≤ variation μ + variation ν := by
  refine variation_le_of_forall_enorm_le fun E _ => ?_
  calc
    _ ≤ ‖μ E‖ₑ + ‖ν E‖ₑ := enorm_add_le _ _
    _ ≤ μ.variation E + ν.variation E := by
      gcongr <;> exact enorm_measure_le_variation _ E

lemma variation_finsetSum_le [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι → VectorMeasure X V) :
    (∑ i ∈ s, μ i).variation ≤ ∑ i ∈ s, (μ i).variation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))

lemma variation_apply_eq_zero (hs : MeasurableSet s) :
    μ.variation s = 0 ↔ ∀ t, t ⊆ s → MeasurableSet t → μ t = 0 := by
  refine ⟨fun h t hts ht ↦ ?_, fun h ↦ ?_⟩
  · rw [← enorm_eq_zero, ← le_zero_iff, ← h]
    apply (enorm_measure_le_variation _ _).trans (measure_mono hts)
  · suffices μ.variation s ≤ (0 : Measure X) s by simpa
    apply variation_apply_le_of_forall_enorm_le hs (fun t ht hts ↦ ?_)
    simp [h t hts ht]

@[simp] lemma variation_eq_zero :
    μ.variation = 0 ↔ μ = 0 where
  mp h := by
    ext s hs
    apply enorm_eq_zero.1
    apply le_antisymm ?_ (by simp)
    grw [enorm_measure_le_variation]
    simp [h]
  mpr h := by simp [h]

lemma variation_restrict (hs : MeasurableSet s) :
    (μ.restrict s).variation = μ.variation.restrict s := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variation (t ∩ s)
    _ ≤ (μ.restrict s).variation (t ∩ s) := by
      apply variation_apply_le_of_forall_enorm_le (ht.inter hs) (fun u u_meas hu ↦ ?_)
      have : μ u = μ.restrict s u :=
        (VectorMeasure.restrict_eq_self _ hs u_meas (hu.trans inter_subset_right)).symm
      rw [this]
      apply enorm_measure_le_variation
    _ ≤ (μ.restrict s).variation t := by
      gcongr
      exact Set.inter_subset_left

lemma variation_restrict_le : (μ.restrict s).variation ≤ μ.variation.restrict s := by
  by_cases hs : MeasurableSet s
  · simp [variation_restrict hs]
  · simp [restrict_not_measurable _ hs, Measure.zero_le]

instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.restrict s).variation :=
  isFiniteMeasure_of_le _ variation_restrict_le

variable {Y : Type*} [MeasurableSpace Y] {φ : X → Y}

lemma variation_map_le : (μ.map φ).variation ≤ μ.variation.map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ, Measure.zero_le]
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  simp [VectorMeasure.map_apply _ hφ hs, Measure.map_apply hφ hs, enorm_measure_le_variation]

instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.map φ).variation :=
  isFiniteMeasure_of_le _ variation_map_le

theorem _root_.MeasurableEmbedding.variation_map (hφ : MeasurableEmbedding φ) :
    (μ.map φ).variation = μ.variation.map φ := by
  apply le_antisymm variation_map_le ?_
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  simp only [hφ.measurable, hs, Measure.map_apply]
  have : (μ.map φ).variation s = (μ.map φ).variation (s ∩ range φ) := by
    nth_rw 1 [← inter_union_sdiff s (range φ)]
    have : (μ.map φ).variation (s \ range φ) = 0 := by
      apply (variation_apply_eq_zero (hs.diff hφ.measurableSet_range)).2 (fun t ht t_meas ↦ ?_)
      have : φ ⁻¹' t = ∅ := by grind
      simp [map_apply, t_meas, hφ.measurable, this]
    rw [measure_union (by grind) (hs.diff hφ.measurableSet_range), this, add_zero]
  rw [this, ← hφ.comap_preimage]
  apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
  simp only [hφ.comap_apply]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  rw [map_apply _ hφ.measurable (hφ.measurableSet_image.2 ht), preimage_image_eq _ hφ.injective]

@[simp] lemma variation_dirac {x : X} {v : V} :
    (VectorMeasure.dirac x v).variation = ‖v‖ₑ • Measure.dirac x := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    by_cases hx : x ∈ s <;> simp [hs, hx]
  · apply Measure.le_iff.2 (fun s hs ↦ ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    by_cases hx : x ∈ s <;> simp [hs, hx]

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ ν : VectorMeasure X V}

theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E ≠ ∞ := by finiteness) :
    ‖μ E‖ ≤ μ.variation.real E := by
  rw [measureReal_def, ← toReal_enorm, ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]

lemma variation_sub_le : (μ - ν).variation ≤ μ.variation + ν.variation := by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]

private lemma variation_smul_le {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation ≤ ‖c‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  simp only [coe_smul, Pi.smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [enorm_measure_le_variation, enorm_eq_nnnorm]

lemma variation_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation = ‖c‖₊ • μ.variation := by
  apply le_antisymm variation_smul_le ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ • μ.variation
  _ = ‖c‖₊ • (c⁻¹ • (c • μ)).variation := by simp [smul_smul, inv_mul_cancel₀ hc]
  _ ≤ ‖c‖₊ • ‖c⁻¹‖₊ • (c • μ).variation := by
    gcongr
    exact variation_smul_le
  _ = (c • μ).variation := by
    simp [smul_smul, mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hc)]

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (c • μ).variation := by
  simp only [variation_smul]
  infer_instance

instance [Finite X] : IsFiniteMeasure μ.variation where
  measure_univ_lt_top := by
    classical
    let : Fintype X := Fintype.ofFinite X
    simp only [variation_apply, preVariation_apply, MeasurableSet.univ, ennrealToMeasure_apply,
      ennrealPreVariation_apply, preVariationFun, ↓reduceDIte, ← sup_univ_eq_ciSup]
    exact (Finset.sup_lt_iff (by simp)).2 (fun b hb ↦ by simp [ENNReal.sum_lt_top, enorm_lt_top])

instance {x : X} {v : V} : IsFiniteMeasure (VectorMeasure.dirac x v).variation := by
  simp only [variation_dirac, enorm_eq_nnnorm, Measure.coe_nnreal_smul]
  infer_instance

@[simp] lemma _root_.MeasureTheory.Measure.variation_toSignedMeasure
    {μ : Measure X} [IsFiniteMeasure μ] :
    μ.toSignedMeasure.variation = μ := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    simp [Measure.toSignedMeasure_apply, hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs ↦ ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [Measure.toSignedMeasure_apply, hs, Measure.real, Real.enorm_eq_ofReal]

/-- For a signed measure, the variation is realized by the norm of the measure of a single set, up
to a factor of `2` and an arbitrarily small error. -/
lemma _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
    (μ : SignedMeasure X) {s : Set X} (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.variation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  /- One may almost realize the variation through a partition into finitely many sets.
  As their measures are real numbers, we can group together those of positive measure, and
  also those of negative measure. This gives two measurable sets. Among these two, the one with the
  largest measure in absolute value satisfies the result. -/
  obtain ⟨P, Ps, P_disj, P_meas, hP⟩ : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧
    ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (∀ t ∈ P, MeasurableSet t) ∧ a < ∑ p ∈ P, ‖μ p‖ₑ := exists_lt_sum_of_lt_variation _ hs ha
  have I : (∑ p ∈ P.filter (fun p ↦ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ := by
    simp only [Real.norm_eq_abs, enorm_eq_nnnorm,
      ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_inj, ← NNReal.coe_inj,
      NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with 0 ≤ μ x, |μ x| = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := calc
      _ = ∑ x ∈ P with 0 ≤ μ x, μ x := by
        apply Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp]
      _ = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := by
        rw [of_biUnion_finset]
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonneg]
    rw [← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  have J : (∑ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ := by
    simp only [not_le, enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_inj, ← NNReal.coe_inj, NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with μ x < 0, |μ x| = - μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := calc
      ∑ x ∈ P with μ x < 0, |μ x|
      _ = ∑ x ∈ P with μ x < 0, -μ x := by
        refine Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp.2.le]
      _ = -μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := by
        rw [of_biUnion_finset]
        · simp
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonpos]
    rw [← neg_nonneg, ← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  simp_rw [two_mul]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p ↦ 0 ≤ μ p), I, J] at hP
  rcases le_total (‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ)
    (‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ) with h | h
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)

end NormedAddCommGroup

end MeasureTheory.VectorMeasure
