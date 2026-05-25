/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Binary
public import Mathlib.Probability.Decision.RiskIncrease

/-!
# Statistical information

## Main definitions

* `deGrootInfo`

## Main statements

* `deGrootInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {π : Measure Bool}

/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π` on `Bool`.
This is the difference of the Bayes risks between estimation without seeing the data and with it. -/
noncomputable
def deGrootInfo (μ ν : Measure 𝓧) (π : Measure Bool) : ℝ≥0∞ :=
  bayesBinaryRisk (Kernel.discard 𝓧 ∘ₘ μ : Measure Unit) (Kernel.discard 𝓧 ∘ₘ ν) π -
    bayesBinaryRisk μ ν π

lemma deGrootInfo_eq_riskIncrease :
  deGrootInfo μ ν π = riskIncrease zeroOneLoss (Kernel.boolKernel μ ν) π := by
  simp only [deGrootInfo, Measure.discard_comp, riskIncrease, Kernel.comp_discard',
    Kernel.boolKernel_apply, bayesBinaryRisk]
  congr with a
  cases a <;> simp

lemma deGrootInfo_eq_min_sub (μ ν : Measure 𝓧) (π : Measure Bool) :
    deGrootInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ) - bayesBinaryRisk μ ν π := by
  simp_rw [deGrootInfo, Measure.discard_comp, bayesBinaryRisk_smul_dirac]

@[simp] lemma deGrootInfo_zero_left : deGrootInfo 0 ν π = 0 := by simp [deGrootInfo]

@[simp] lemma deGrootInfo_zero_right : deGrootInfo μ 0 π = 0 := by simp [deGrootInfo]

@[simp] lemma deGrootInfo_zero_prior : deGrootInfo μ ν 0 = 0 := by simp [deGrootInfo]

@[simp] lemma deGrootInfo_self : deGrootInfo μ μ π = 0 := by simp [deGrootInfo]

lemma deGrootInfo_le_min : deGrootInfo μ ν π ≤ min (π {false} * μ univ) (π {true} * ν univ) :=
  deGrootInfo_eq_min_sub μ ν π ▸ tsub_le_self

lemma deGrootInfo_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure π] : deGrootInfo μ ν π ≠ ⊤ :=
  (deGrootInfo_le_min.trans_lt <| min_lt_iff.mpr <| Or.inl
    <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)).ne

lemma deGrootInfo_comm : deGrootInfo μ ν π = deGrootInfo ν μ (π.map Bool.not) := by
  simp_rw [deGrootInfo, bayesBinaryRisk_comm _ _ π]

lemma deGrootInfo_of_measure_true_eq_zero (μ ν : Measure 𝓧) (hπ : π {true} = 0) :
    deGrootInfo μ ν π = 0 :=
  le_antisymm (deGrootInfo_le_min.trans (by simp [hπ])) zero_le'

lemma deGrootInfo_of_measure_false_eq_zero (μ ν : Measure 𝓧) (hπ : π {false} = 0) :
    deGrootInfo μ ν π = 0 :=
  le_antisymm (deGrootInfo_le_min.trans (by simp [hπ])) zero_le'

/-- **Data processing inequality** for the statistical information. -/
lemma deGrootInfo_comp_le (μ ν : Measure 𝓧) (π : Measure Bool) (η : Kernel 𝓧 𝓨) [IsMarkovKernel η] :
    deGrootInfo (η ∘ₘ μ) (η ∘ₘ ν) π ≤ deGrootInfo μ ν π := by
  simp_rw [deGrootInfo_eq_riskIncrease, ← Kernel.comp_boolKernel]
  exact riskIncrease_comp_le zeroOneLoss (Kernel.boolKernel μ ν) π η

/-- **Data processing inequality** for the statistical information. -/
lemma deGrootInfo_map_le (μ ν : Measure 𝓧) (π : Measure Bool) {f : 𝓧 → 𝓨} (hf : Measurable f) :
    deGrootInfo (μ.map f) (ν.map f) π ≤ deGrootInfo μ ν π := by
  rw [← Measure.deterministic_comp_eq_map hf, ← Measure.deterministic_comp_eq_map hf]
  exact deGrootInfo_comp_le μ ν π (Kernel.deterministic f hf)

lemma deGrootInfo_eq_deGrootInfo_one_one :
    deGrootInfo μ ν π = deGrootInfo (π {false} • μ) (π {true} • ν) (boolMeasure 1 1) := by
  rw [deGrootInfo, bayesBinaryRisk_eq_bayesBinaryRisk_one_one]
  nth_rw 2 [bayesBinaryRisk_eq_bayesBinaryRisk_one_one]
  simp [deGrootInfo]

lemma deGrootInfo_boolMeasure_le_deGrootInfo {E : Set 𝓧} (hE : MeasurableSet E) :
    deGrootInfo (boolMeasure (μ Eᶜ) (μ E)) (boolMeasure (ν Eᶜ) (ν E)) π
      ≤ deGrootInfo μ ν π := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    (Measurable.of_discrete.fun_comp (measurable_one.indicator hE))
  let η : Kernel 𝓧 Bool := Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x)) h_meas
  have h_false : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext x; simp [Bool.ofNat]
  have h_true : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext x; simp [Bool.ofNat]
  convert deGrootInfo_comp_le μ ν π η <;>
  · refine Measure.ext_of_singleton fun b ↦ ?_
    rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas (by trivial)]
    cases b <;> simp [h_false, h_true]

lemma deGrootInfo_eq_min_sub_lintegral (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    deGrootInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [deGrootInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_min]

lemma deGrootInfo_eq_min_sub_lintegral' {ζ : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    deGrootInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * (∂μ/∂ζ) x) (π {true} * (∂ν/∂ζ) x) ∂ζ := by
  by_cases h_false : π {false} = 0
  · simp [deGrootInfo_of_measure_false_eq_zero, h_false]
  by_cases h_true : π {true} = 0
  · simp [deGrootInfo_of_measure_true_eq_zero, h_true]
  have hμac : μ ≪ Kernel.boolKernel μ ν ∘ₘ π :=
    absolutelyContinuous_boolKernel_comp_left μ ν h_false
  have hνac : ν ≪ Kernel.boolKernel μ ν ∘ₘ π :=
    absolutelyContinuous_boolKernel_comp_right μ ν h_true
  have hacζ : Kernel.boolKernel μ ν ∘ₘ π ≪ ζ :=
    boolKernel_comp_measure μ ν π ▸ (hνζ.smul_left _).add_left (hμζ.smul_left _)
  rw [deGrootInfo_eq_min_sub_lintegral, ← lintegral_rnDeriv_mul hacζ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hμac, Measure.rnDeriv_mul_rnDeriv hνac] with x hxμ hxν
  rw [mul_min, mul_comm, mul_comm _ (π _ * _), mul_assoc, mul_assoc]
  congr

lemma toReal_deGrootInfo_eq_min_sub_integral (μ ν : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (deGrootInfo μ ν π).toReal
      = min (π.real {false} * μ.real univ) (π.real {true} * ν.real univ)
        - ∫ x, min (π.real {false} * (μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
          (π.real {true} * (ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [deGrootInfo_eq_min_sub, ENNReal.toReal_sub_of_le (bayesBinaryRisk_le_min μ ν π),
    ENNReal.toReal_min (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    toReal_bayesBinaryRisk_eq_integral_min]
  · rfl
  · have hμ : π {false} * μ univ ≠ ⊤ := by finiteness
    have hν : π {true} * ν univ ≠ ⊤ := by finiteness
    simp [hμ, hν]

lemma deGrootInfo_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    deGrootInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  rw [deGrootInfo_eq_min_sub, bayesBinaryRisk_eq_iInf_measurableSet]

lemma deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π]
    (h : π {true} * ν univ ≤ π {false} * μ univ) :
    deGrootInfo μ ν π = ⨆ E, ⨆ (_ : MeasurableSet E), π {true} * ν E - π {false} * μ E := by
  rw [deGrootInfo_eq_min_sub_iInf_measurableSet, min_eq_right h]
  calc π {true} * ν univ - ⨅ (E) (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ
  _ = π {true} * ν univ - ⨅ (E) (_ : MeasurableSet E), π {false} * μ E +
      (π {true} * ν univ - π {true} * ν E) := by
    congr with E
    congr with hE
    congr
    rw [measure_compl hE (measure_ne_top _ _), ENNReal.mul_sub (by simp)]
  _ = ⨆ (E) (_ : MeasurableSet E), π {true} * ν E - π {false} * μ E := by
    simp_rw [ENNReal.sub_iInf]
    congr with E
    congr with hE
    rcases le_total (π {true} * ν E) (π {false} * μ E) with hE_le | hE_le
    · rw [tsub_eq_zero_of_le hE_le]
      refine tsub_eq_zero_of_le ?_
      calc π {true} * ν univ
      _ = π {true} * ν E + (π {true} * ν univ - π {true} * ν E) := by
        rw [add_comm, ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
        · finiteness
        · have : E ⊆ univ := subset_univ E
          gcongr
        · finiteness
      _ ≤ π {false} * μ E + (π {true} * ν univ - π {true} * ν E) := by gcongr
    · rw [add_comm]
      calc π {true} * ν univ - (π {true} * ν univ - π {true} * ν E + π {false} * μ E)
      _ = (π {true} * ν univ - π {true} * ν E + π {true} * ν E)
          - (π {true} * ν univ - π {true} * ν E + π {false} * μ E) := by
        congr
        rw [ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
        · finiteness
        · have : E ⊆ univ := subset_univ E
          gcongr
        · finiteness
      _ = π {true} * ν E - π {false} * μ E := by
        rw [ENNReal.add_sub_add_eq_sub_left (by finiteness)]

lemma deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le' (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π]
    (h : π {false} * μ univ ≤ π {true} * ν univ) :
    deGrootInfo μ ν π = ⨆ E, ⨆ (_ : MeasurableSet E), π {false} * μ E - π {true} * ν E := by
  rw [deGrootInfo_comm, deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le]
  · simp
  · simpa using h

lemma deGrootInfo_eq_zero_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (hνμ : π {true} • ν ≤ π {false} • μ) :
    deGrootInfo μ ν π = 0 := by
  have h_le s : π {true} * ν s ≤ π {false} * μ s := hνμ s
  rw [deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le _ _ _ (h_le .univ)]
  simp [tsub_eq_zero_iff_le, h_le]

lemma deGrootInfo_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (h_univ : π {false} * μ univ = π {true} * ν univ) :
    deGrootInfo μ ν π = 0 ↔ π {false} • μ = π {true} • ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (by finiteness)
    have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (by finiteness)
    refine Measure.eq_of_le_of_measure_univ_eq ?_ (by simp [h_univ])
    refine Measure.le_intro fun s hs _ ↦ ?_
    rw [deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le' _ _ _ h_univ.le] at h
    simp only [ENNReal.iSup_eq_zero, tsub_eq_zero_iff_le] at h
    exact h s hs
  · rw [deGrootInfo_eq_deGrootInfo_one_one, h, deGrootInfo_self]

lemma toReal_deGrootInfo_eq_integral_abs_boolKernel (μ ν : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {π : Measure Bool} [IsFiniteMeasure π] :
    (deGrootInfo μ ν π).toReal
      = 2⁻¹ * (-|π.real {false} * μ.real univ - π.real {true} * ν.real univ|
        + ∫ x, |π.real {false} * (μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - π.real {true} * (ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|
          ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  rw [deGrootInfo_eq_min_sub, ENNReal.toReal_sub_of_le]
  rotate_left
  · exact bayesBinaryRisk_le_min μ ν π
  · exact ne_top_of_le_ne_top (by finiteness) (min_le_left _ _)
  rw [toReal_bayesBinaryRisk_eq_integral_abs,
    ENNReal.toReal_min (by finiteness) (by finiteness), min_eq_add_sub_abs_sub]
  simp only [ENNReal.toReal_mul, Measure.real]
  ring

-- -- used to show equality to an f-divergence
-- lemma toReal_deGrootInfo_eq_integral_abs (μ ν : Measure 𝓧)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] {π : Measure Bool} [IsFiniteMeasure π] :
--     (deGrootInfo μ ν π).toReal
--       = 2⁻¹ * (-|(π {false} * μ univ).toReal - (π {true} * ν univ).toReal|
--         + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν
--         + (π {false} * (μ.singularPart ν) univ).toReal) := by
--   sorry

end ProbabilityTheory
