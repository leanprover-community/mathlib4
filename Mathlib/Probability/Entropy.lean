/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy of a measure

For a probability measure, the entropy is the quantity `-∑' s, (μ {s}).toReal * log (μ {s}).toReal`.

## Main definitions

* `measureEntropy`: entropy of a measure `μ`, denoted by `Hm[μ]`.

## Notations

* `Hm[μ] = measureEntropy μ`.

-/

open MeasureTheory Real BigOperators NNReal ENNReal

namespace ProbabilityTheory

variable {S T : Type*} {mS : MeasurableSpace S} {mT : MeasurableSpace T}
  {μ : Measure S} {ν : Measure T}

/-- Entropy of a measure. For a probability measure, this is the quantity
`- ∑' s, (μ {s}).toReal * log (μ {s}).toReal`.
Notation: `Hm[μ]`.

We extend the definition to finite measures by normalizing the measure by `(μ Set.univ)⁻¹`.
If `μ` is a probability measure, a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal

@[inherit_doc measureEntropy] notation3:100 "Hm[" μ "]" => measureEntropy μ

lemma measureEntropy_def (μ : Measure S) :
    measureEntropy μ = ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal := rfl

lemma measureEntropy_eq_sum_finset {A : Finset S} (hA : μ Aᶜ = 0) :
    Hm[μ] = ∑ s in A, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ {s} = 0 by simp [this]
  apply measure_mono_null _ hA
  simpa

lemma measureEntropy_of_fintype [Fintype S] (μ : Measure S) :
    Hm[μ] = ∑ s, negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal := by
  rw [measureEntropy_eq_sum_finset (A := Finset.univ)]
  simp

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ {s}).toReal := by
  simp [measureEntropy]

lemma measureEntropy_eq_sum_finset_of_isProbabilityMeasure {A : Finset S} (hA : μ Aᶜ = 0)
    [IsProbabilityMeasure μ] :
    Hm[μ] = ∑ s in A, negMulLog (μ {s}).toReal := by
  rw [measureEntropy_eq_sum_finset hA]
  simp

lemma measureEntropy_of_fintypeof_isProbabilityMeasure [Fintype S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ {s}).toReal := by
  rw [measureEntropy_eq_sum_finset_of_isProbabilityMeasure (A := Finset.univ)]
  simp

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

@[simp]
lemma measureEntropy_dirac [MeasurableSingletonClass S] (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy_def]
  simp only [MeasurableSet.univ, Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem,
    Pi.one_apply, inv_one, one_smul, MeasurableSet.singleton, Set.mem_singleton_iff]
  rw [tsum_eq_single x]
  · simp
  · simp only [Finset.mem_univ, ne_eq, Set.mem_singleton_iff, forall_true_left]
    intro b hb
    simp [Ne.symm hb]

@[simp]
lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · cases eq_zero_or_neZero μ with
    | inl hμ => simp [hμ]
    | inr hμ =>
      rw [measureEntropy_def]
      simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
        ENNReal.toReal_mul]
      rw [ENNReal.inv_mul_cancel]
      · simp only [inv_one, ENNReal.one_toReal, one_mul]
        simp [measureEntropy]
      · simp [hμ.out]
      · exact measure_ne_top _ _
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  apply tsum_nonneg
  intro s
  apply negMulLog_nonneg (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

lemma measureEntropy_le_card_aux [MeasurableSingletonClass S] [IsProbabilityMeasure μ]
    (A : Finset S) (hμ : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have μA : μ A = 1 := by
    rw [← compl_compl (A : Set S), measure_compl A.measurableSet.compl (measure_ne_top _ _), hμ]
    simp
  let N := A.card
  have N_pos : (0 : ℝ) < N := by
    rcases Finset.eq_empty_or_nonempty A with rfl|hA
    · simp at μA
    · simpa using Finset.card_pos.mpr hA
  simp only [measureEntropy_def, measure_univ, inv_one, one_smul]
  calc
  ∑' x, negMulLog (μ {x}).toReal
    = ∑ x in A, negMulLog (μ {x}).toReal := by
      apply tsum_eq_sum
      intro i hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [this]
  _ = N * ∑ x in A, (N : ℝ)⁻¹ * negMulLog (μ {x}).toReal := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x in A, (N : ℝ)⁻¹ * (μ {x}).toReal) :=
      mul_le_mul_of_nonneg_left
        (concaveOn_negMulLog.le_map_sum (by simp) (by simp [mul_inv_cancel N_pos.ne']) (by simp))
        (by positivity)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum, μA]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel N_pos.ne']

lemma measureEntropy_le_log_card_of_mem [MeasurableSingletonClass S]
    {A : Finset S} (hμA : μ Aᶜ = 0) :
    Hm[μ] ≤ log (Nat.card A) := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_nat_cast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp [h_log_card_nonneg]; positivity
  · by_cases hμ_fin : IsFiniteMeasure μ
    swap;
    · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
      exact h_log_card_nonneg
    rw [← measureEntropy_univ_smul]
    have : ((μ Set.univ) ⁻¹ • μ) (Aᶜ) = 0 := by simp [hμA]
    convert measureEntropy_le_card_aux A this using 3
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe A

lemma measureEntropy_map_of_injective [MeasurableSingletonClass T]
    (μ : Measure S) (f : S → T) (hf_m : Measurable f) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy_def, Measure.smul_apply,
    Measure.map_apply hf_m (measurableSet_singleton _), this]
  classical
  let F : T → ℝ := fun x ↦ negMulLog ((μ Set.univ)⁻¹ • μ (f ⁻¹' {x})).toReal
  have : ∑' x : T, F x = ∑' x : (f '' Set.univ), F x := by
    refine (tsum_subtype_eq_of_support_subset (fun x hx ↦ ?_)).symm
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ (Set.injective_iff_injOn_univ.mp hf), tsum_univ (fun x ↦ F (f x))]
  congr! with s
  ext s'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact hf.eq_iff

lemma measureEntropy_comap [MeasurableSingletonClass T] {f : T → S}
    (hf : MeasurableEmbedding f) (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    Hm[μ.comap f] = Hm[μ] := by
  simp_rw [measureEntropy_def, Measure.smul_apply,
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ (measurableSet_singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul, ENNReal.toReal_mul]
  classical
  rw [← tsum_range (f := fun x ↦ negMulLog (((μ (Set.range f))⁻¹).toReal * (μ {x}).toReal))
    (g := f) hf.injective, measure_congr hf_range]
  let F : S → ℝ := fun x ↦ negMulLog (((μ (Set.univ))⁻¹).toReal * (μ {x}).toReal)
  change ∑' x : (Set.range f), F x = ∑' x : S, F x
  refine tsum_subtype_eq_of_support_subset (fun x hx ↦ ?_)
  contrapose hx
  suffices μ {x} = 0 by simp [this]
  refine measure_mono_null (fun y' ↦ ?_) hf_range
  simp only [Set.mem_singleton_iff, eq_iff_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
  rintro rfl
  contrapose! hx
  have : Set.univ y' := by exact trivial
  rwa [← hx] at this

lemma measureEntropy_comap_equiv [MeasurableSingletonClass T] (μ : Measure S) (f : T ≃ᵐ S) :
    Hm[μ.comap f] = Hm[μ] := by
  refine measureEntropy_comap f.measurableEmbedding ?_
  simp only [ae_eq_univ]
  have : Set.range f = Set.univ := Equiv.range_eq_univ _
  simp [this]

section Fintype

variable [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass T] [Fintype T]

lemma measureEntropy_le_log_card (μ : Measure S) : Hm[μ] ≤ log (Fintype.card S) := by
  convert measureEntropy_le_log_card_of_mem (A := (Finset.univ : Finset S)) (by simp)
  simp only [Finset.mem_univ, Nat.card_eq_fintype_card, Fintype.subtype_card,
    Finset.filter_congr_decidable, forall_true_left, implies_true, Finset.filter_true_of_mem]
  rfl

lemma measureEntropy_eq_card_iff_measure_eq_aux' (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s, (μ {s}).toReal = (Fintype.card S : ℝ)⁻¹ := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  | inr h =>
    -- multiply the left-hand side by `N⁻¹`
    set N := Fintype.card S
    have hN : 0 < (N : ℝ)⁻¹ := by simp only [inv_pos, Nat.cast_pos, Fintype.card_pos]
    rw [← mul_right_inj' hN.ne']
    -- setup to use equality case of Jensen's inequality
    let w (_ : S) := (N : ℝ)⁻¹
    have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; exact hN
    have hw2 : ∑ s : S, w s = 1 := by simp [Finset.card_univ]
    have hp : ∀ s ∈ Finset.univ, 0 ≤ (μ {s}).toReal := by intros; positivity
    -- use equality case of Jensen's inequality
    convert eq_comm.trans <| strictConcaveOn_negMulLog.map_sum_eq_iff hw1 hw2 hp using 2
    · rw [measureEntropy_def, tsum_fintype, Finset.mul_sum]
      simp
    · simp [negMulLog, ← Finset.mul_sum]
    · simp only [Finset.mem_univ, smul_eq_mul, forall_true_left]
      rw [← Finset.mul_sum]
      simp

lemma measureEntropy_eq_card_iff_measure_eq_aux (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s, μ {s} = (Fintype.card S : ℝ≥0)⁻¹) := by
  rw [measureEntropy_eq_card_iff_measure_eq_aux']
  congr! with s
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  congr!
  simp

lemma measureEntropy_eq_card_iff_measure_eq' [IsFiniteMeasure μ] [h0 : NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔
      ∀ s, (μ {s}).toReal = (μ Set.univ).toReal / Fintype.card S := by
  rw [← measureEntropy_univ_smul]
  convert measureEntropy_eq_card_iff_measure_eq_aux' ((μ Set.univ)⁻¹ • μ) using 2 with s
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
    toReal_mul]
  rw [ENNReal.toReal_inv, inv_mul_eq_iff_eq_mul₀ ?_, div_eq_mul_inv]
  simp [ENNReal.toReal_ne_zero, h0.out, measure_ne_top]

lemma measureEntropy_eq_card_iff_measure_eq [IsFiniteMeasure μ] [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s, μ {s} = μ Set.univ / Fintype.card S := by
  obtain h | h := isEmpty_or_nonempty S
  · have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  rw [div_eq_mul_inv, measureEntropy_eq_card_iff_measure_eq']
  congr! with s
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  · exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)

@[simp]
lemma measureEntropy_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_sum, Fintype.sum_prod_type]
  swap; · simp
  simp_rw [← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul, negMulLog_mul,
    Finset.sum_add_distrib]
  congr
  · rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_sum (s := Finset.univ)]
    congr with x
    rw [← Finset.sum_mul]
    simp only [Finset.sum_toReal_measure_singleton, Finset.coe_univ, measure_univ, one_toReal,
      one_mul]
    simp
  · rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_sum (s := Finset.univ)]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [Finset.sum_toReal_measure_singleton, Finset.coe_univ, measure_univ, one_toReal,
      one_mul]
    simp

end Fintype

end ProbabilityTheory
