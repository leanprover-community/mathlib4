/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Decision.Binary

/-!
# Statistical information

## Main definitions

* `statInfo`

## Main statements

* `statInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 𝓧' : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'}
  {μ ν : Measure 𝓧} {π : Measure Bool}

/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π ∈ ℳ({0,1})`. -/
noncomputable
def statInfo (μ ν : Measure 𝓧) (π : Measure Bool) : ℝ≥0∞ :=
  bayesBinaryRisk (Kernel.discard 𝓧 ∘ₘ μ) (Kernel.discard 𝓧 ∘ₘ ν) π - bayesBinaryRisk μ ν π

lemma statInfo_eq_min_sub (μ ν : Measure 𝓧) (π : Measure Bool) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ) - bayesBinaryRisk μ ν π := by
  simp_rw [statInfo, Measure.discard_comp, bayesBinaryRisk_dirac]

@[simp] lemma statInfo_zero_left : statInfo 0 ν π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_right : statInfo μ 0 π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_prior : statInfo μ ν 0 = 0 := by simp [statInfo]

@[simp] lemma statInfo_self : statInfo μ μ π = 0 := by simp [statInfo]

lemma statInfo_le_min : statInfo μ ν π ≤ min (π {false} * μ univ) (π {true} * ν univ) :=
  statInfo_eq_min_sub μ ν π ▸ tsub_le_self

lemma statInfo_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure π] :
    statInfo μ ν π ≠ ⊤ :=
  (statInfo_le_min.trans_lt <| min_lt_iff.mpr <| Or.inl
    <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)).ne

lemma statInfo_symm : statInfo μ ν π = statInfo ν μ (π.map Bool.not) := by
  simp_rw [statInfo, bayesBinaryRisk_symm _ _ π]

lemma statInfo_of_measure_true_eq_zero (μ ν : Measure 𝓧) (hπ : π {true} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le'

lemma statInfo_of_measure_false_eq_zero (μ ν : Measure 𝓧) (hπ : π {false} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le'

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝓧) (π : Measure Bool) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    statInfo (η ∘ₘ μ) (η ∘ₘ ν) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)
  simp [Measure.bind_apply .univ (Kernel.aemeasurable _)]

lemma statInfo_boolMeasure_le_statInfo {E : Set 𝓧} (hE : MeasurableSet E) :
    statInfo (Bool.boolMeasure (μ Eᶜ) (μ E)) (Bool.boolMeasure (ν Eᶜ) (ν E)) π
      ≤ statInfo μ ν π := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    (Measurable.of_discrete.comp' (measurable_one.indicator hE))
  let η : Kernel 𝓧 Bool := Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x)) h_meas
  have h_false : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext x; simp [Bool.ofNat]
  have h_true : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext x; simp [Bool.ofNat]
  convert statInfo_comp_le μ ν π η <;>
  · ext
    · rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas (by trivial), h_false,
        Bool.boolMeasure_apply_false]
    · rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas (by trivial), h_true,
        Bool.boolMeasure_apply_true]

lemma statInfo_eq_min_sub_lintegral (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * μ.rnDeriv (boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (boolKernel μ ν ∘ₘ π) x) ∂(boolKernel μ ν ∘ₘ π) := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_min]

lemma ENNReal.mul_min (a b c : ℝ≥0∞) : a * min b c = min (a * b) (a * c) := mul_left_mono.map_min

lemma statInfo_eq_min_sub_lintegral' {ζ : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * (∂μ/∂ζ) x) (π {true} * (∂ν/∂ζ) x) ∂ζ := by
  by_cases h_false : π {false} = 0
  · simp [statInfo, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero]
  have hμac : μ ≪ (boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_measure_left μ ν h_false
  have hνac : ν ≪ (boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_measure_right μ ν h_true
  have hacζ : (boolKernel μ ν ∘ₘ π) ≪ ζ :=
    boolKernel_comp_measure μ ν π ▸ (hνζ.smul_left _).add_left (hμζ.smul_left _)
  rw [statInfo_eq_min_sub_lintegral, ← lintegral_rnDeriv_mul hacζ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hμac, Measure.rnDeriv_mul_rnDeriv hνac] with x hxμ hxν
  rw [ENNReal.mul_min, mul_comm, mul_comm _ (π _ * _), mul_assoc, mul_assoc]
  congr

lemma statInfo_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_iInf_measurableSet]

end ProbabilityTheory
