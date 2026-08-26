/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
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
* `ennrealVariation_eq_self`: if `μ : VectorMeasure X ℝ≥0∞` then `μ.ennrealVariation = μ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset Set
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

/-- The sum of a vector measure `μ` on a `Finpartition` of `Subtype MeasurableSet` equals `μ s`. -/
lemma sum_finpartition [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
    (μ : VectorMeasure X V) {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p ∈ P.parts, μ p.val = μ s := by
  rw [← μ.of_biUnion_finset (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl) (fun p _ => p.prop),
      ← Finset.sup_set_eq_biUnion, P.sup_parts_apply (fun _ _ => rfl) rfl]

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
  swap; · simp [hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, zero_apply, enorm_zero]
  exact preVariation_zero

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable hsm

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

@[simp] lemma variation_apply_singleton {x : X} [MeasurableSingletonClass X] :
    μ.variation {x} = ‖μ {x}‖ₑ := by
  apply le_antisymm ?_ (enorm_measure_le_variation μ {x})
  rw [show ‖μ {x}‖ₑ = (‖μ {x}‖ₑ • Measure.dirac x) {x} by simp]
  apply variation_apply_le_of_forall_enorm_le (.singleton x) (fun s hs h's ↦ ?_)
  obtain rfl | rfl := s.subset_singleton_iff_eq.1 h's <;> simp

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
  simp only [smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
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
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs ↦ ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]

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

section ENormedAddCommGroup

variable {V : Type*} [NormedAddCommGroup V]

@[simp] lemma variation_zero_iff_univ (μ : VectorMeasure X V) :
    μ.variation Set.univ = 0 ↔ μ = 0 := by
  simp

noncomputable instance : EMetricSpace (VectorMeasure X V) where
  edist μ ν := (μ - ν).variation Set.univ
  edist_self := by intro; simp
  edist_comm := by
    intro _ _
    rw [← variation_neg]
    simp
  edist_triangle := by
    intro x y z
    simpa using Measure.le_iff.mp (variation_add_le (μ := x - y) (ν := y - z))
      Set.univ MeasurableSet.univ
  eq_of_edist_eq_zero {x y} h := by
    rw [variation_zero_iff_univ] at h
    exact eq_of_sub_eq_zero h

lemma edist_eq_variation_sub (μ ν : VectorMeasure X V) :
    edist μ ν = (μ - ν).variation Set.univ := by rfl

noncomputable instance : ENormedAddCommMonoid (VectorMeasure X V) where
  enorm μ := μ.variation Set.univ
  continuous_enorm := by
    have : Continuous (fun x : VectorMeasure X V ↦ edist x 0) := by continuity
    simpa [edist_eq_variation_sub, sub_zero] using this
  enorm_zero := by simp
  enorm_add_le x y := by
    simpa using Measure.le_iff.mp (variation_add_le (μ := x) (ν := y)) Set.univ MeasurableSet.univ
  enorm_eq_zero x := variation_zero_iff_univ _

end ENormedAddCommGroup

section mapRangeL
variable {V : Type*} [NormedAddCommGroup V] {W : Type*} [NormedAddCommGroup W]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

/-- Given a continuous linear map `f : M → N`, `mapRangeL` is the continuous linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeL (f : V →L[𝕜] W) : VectorMeasure X V →L[𝕜] VectorMeasure X W where
  toFun v := v.mapRange f.toAddMonoidHom f.continuous
  map_add' _ _ := mapRange_add f.continuous
  map_smul' _ _ := mapRange_smul f.continuous
  cont := by
    apply LipschitzWith.continuous (K := ‖f‖₊)
    -- generalize this to `continuous_of_bound` for `ENormedAddCommMonoid`
    intro μ ν
    rw [edist_eq_variation_sub, edist_eq_variation_sub]
    have hsub : μ.mapRange f.toAddMonoidHom f.continuous -
        ν.mapRange f.toAddMonoidHom f.continuous =
        (μ - ν).mapRange f.toAddMonoidHom f.continuous := by
      ext s
      change f (μ s) - f (ν s) = f ((μ - ν) s)
      simp
    rw [hsub]
    change ((μ - ν).mapRange f.toAddMonoidHom f.continuous).variation Set.univ ≤ _
    -- write the lemma `variation_mapRangeₗ` and insert it here
    have hv : ((μ - ν).mapRange f.toAddMonoidHom f.continuous).variation ≤
        ‖f‖₊ • (μ - ν).variation := by
      apply variation_le_of_forall_enorm_le
      intro s hs
      change ‖f ((μ - ν) s)‖ₑ ≤ (‖f‖₊ • (μ - ν).variation) s
      calc
        _ ≤ ‖f‖₊ * ‖(μ - ν) s‖ₑ := f.le_opENorm _
        _ ≤ ‖f‖₊ * (μ - ν).variation s := by
          gcongr
          exact enorm_measure_le_variation _ _
        _ = _ := by simp
    simpa using Measure.le_iff.mp hv Set.univ MeasurableSet.univ

@[simp]
lemma mapRangeL_apply (μ : VectorMeasure X V) {f : V →L[𝕜] W} {s : Set X} :
    μ.mapRangeL f s = f (μ s) := by
  unfold mapRangeL
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  rfl

lemma variation_mapRangeL {W 𝕜 : Type*} [NormedAddCommGroup W] [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] (μ : VectorMeasure X V) (f : V →L[𝕜] W) :
    (μ.mapRangeL f).variation ≤ ‖f‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  calc
    ‖f (μ s)‖ₑ ≤ ‖f‖₊ * ‖μ s‖ₑ := f.le_opENorm _
    _ ≤ ‖f‖₊ * μ.variation s := by
        gcongr; exact enorm_measure_le_variation μ s

end mapRangeL

section ENNReal

variable (μ : VectorMeasure X ℝ≥0∞)

/-- For `μ : VectorMeasure X ℝ≥0∞` and measurable `s`, the supremum over Finpartitions of
`⟨s, hs⟩ : Subtype MeasurableSet` of the sum of `μ` over parts equals `μ s`. -/
@[simp]
lemma iSup_sum_finpartition_parts {s : Set X} (hs : MeasurableSet s) :
    ⨆ (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, μ p.val = μ s := by
  simp_rw [μ.sum_finpartition, iSup_const]

/-- For `μ : VectorMeasure X ℝ≥0∞`, `preVariationFun μ s = μ s` for any `s`. -/
lemma preVariationFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s := by
  by_cases h : MeasurableSet s
  · rw [preVariationFun_apply]
    exact iSup_sum_finpartition_parts μ h
  · rw [preVariationFun_of_not_measurableSet μ h, not_measurable μ h]

theorem variation_eq_ennrealToMeasure : μ.variation = μ.ennrealToMeasure := by
  ext _ hs
  simp [preVariationFun_apply_of_ennreal, variation_apply, preVariation_apply,
    ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]
theorem ennrealVariation_eq_self : μ.ennrealVariation = μ := by
  simp [variation_eq_ennrealToMeasure, ennrealVariation]

end ENNReal

end MeasureTheory.VectorMeasure
