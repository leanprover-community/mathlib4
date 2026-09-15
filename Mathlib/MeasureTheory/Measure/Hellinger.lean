/-
Copyright (c) 2026 Daniel Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Rodriguez
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hellinger affinity of a pair of measures

The Hellinger affinity (also known as the Bhattacharyya coefficient) of two measures `μ` and `ν`
is `∫ √(dμ/dρ · dν/dρ) dρ` for a dominating measure `ρ`. We define it against the canonical
dominating measure `ρ = μ + ν`, which makes the definition total: no absolute-continuity or
integrability hypothesis is needed, and the value does not depend on the choice of dominating
measure (`hellingerAffinity_eq_lintegral_rnDeriv_mul_rnDeriv`).

The affinity is an f-integral: it equals `∫⁻ f (dμ/dν) dν` for `f = √·` (suitably interpreted
against a common dominating measure), so it fits the f-divergence family; once a general `fDiv`
framework is available in Mathlib, a bridging lemma relating `hellingerAffinity` to the
corresponding f-divergence should be added here.

This file is groundwork for Kakutani's dichotomy (1948) on equivalence and singularity of
infinite products of probability measures, where the affinity is the quantity whose infinite
product decides the dichotomy.

## Main definitions

* `MeasureTheory.Measure.hellingerAffinity`: the Hellinger affinity of two measures, `ℝ≥0∞`-valued,
  defined as `∫⁻ x, √(dμ/d(μ + ν) · dν/d(μ + ν)) ∂(μ + ν)`.

## Main results

* `MeasureTheory.Measure.hellingerAffinity_eq_lintegral_rnDeriv_mul_rnDeriv`: the affinity can be
  computed against any σ-finite dominating measure `ρ` as
  `∫⁻ x, (dμ/dρ · dν/dρ) ^ (1/2) ∂ρ`.
* `MeasureTheory.Measure.hellingerAffinity_le_one`: the affinity of two probability measures is
  at most `1`, by Hölder's inequality with exponents `p = q = 2`.
* `MeasureTheory.Measure.hellingerAffinity_eq_zero_iff`: the affinity of two finite measures
  vanishes if and only if they are mutually singular.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace Measure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- The **Hellinger affinity** (Bhattacharyya coefficient) of two measures:
`∫ √(dμ/dρ · dν/dρ) dρ` computed against the canonical dominating measure
`ρ = μ + ν`. Total and symmetric; no absolute-continuity hypothesis. -/
noncomputable def hellingerAffinity (μ ν : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) ∂(μ + ν)

/-- The Hellinger affinity is symmetric in its two arguments. -/
lemma hellingerAffinity_comm (μ ν : Measure Ω) :
    hellingerAffinity μ ν = hellingerAffinity ν μ := by
  rw [hellingerAffinity, hellingerAffinity, add_comm ν μ]
  exact lintegral_congr fun x => by rw [mul_comm]

/-- `(c * c) ^ (1/2) = c` in `ℝ≥0∞` — no finiteness hypothesis needed. -/
private lemma mul_self_rpow_half (c : ℝ≥0∞) : (c * c) ^ (1 / 2 : ℝ) = c := by
  rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Invariance under the choice of dominating measure**: for finite `μ`, `ν`
and any σ-finite `ρ` dominating both, the Hellinger affinity is computed by
the `ρ`-integral of `√(dμ/dρ · dν/dρ)`. -/
theorem hellingerAffinity_eq_lintegral_rnDeriv_mul_rnDeriv
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ρ : Measure Ω} [SigmaFinite ρ]
    (hμρ : μ ≪ ρ) (hνρ : ν ≪ ρ) :
    hellingerAffinity μ ν
      = ∫⁻ x, (μ.rnDeriv ρ x * ν.rnDeriv ρ x) ^ (1 / 2 : ℝ) ∂ρ := by
  have hσρ : μ + ν ≪ ρ := hμρ.add_left hνρ
  have hμσ : μ ≪ μ + ν := AbsolutelyContinuous.rfl.add_right ν
  have hνσ : ν ≪ μ + ν := AbsolutelyContinuous.rfl.add_right' μ
  have h1 := Measure.rnDeriv_mul_rnDeriv (κ := ρ) hμσ
  have h2 := Measure.rnDeriv_mul_rnDeriv (κ := ρ) hνσ
  have hm : Measurable fun x =>
      (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_rnDeriv _ _).mul (measurable_rnDeriv _ _))
  rw [hellingerAffinity, ← MeasureTheory.lintegral_rnDeriv_mul hσρ hm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Pi.mul_apply] at hx1 hx2
  rw [← hx1, ← hx2]
  have key : ∀ a b c : ℝ≥0∞,
      (a * c * (b * c)) ^ (1 / 2 : ℝ) = c * (a * b) ^ (1 / 2 : ℝ) := by
    intro a b c
    rw [show a * c * (b * c) = a * b * (c * c) from by ring,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_self_rpow_half, mul_comm]
  exact (key _ _ _).symm

/-- The Hellinger affinity of a probability measure with itself is `1`. -/
lemma hellingerAffinity_self [IsProbabilityMeasure μ] :
    hellingerAffinity μ μ = 1 := by
  calc hellingerAffinity μ μ
      = ∫⁻ x, (μ.rnDeriv μ x * μ.rnDeriv μ x) ^ (1 / 2 : ℝ) ∂μ :=
        hellingerAffinity_eq_lintegral_rnDeriv_mul_rnDeriv .rfl .rfl
    _ = ∫⁻ _, 1 ∂μ := lintegral_congr_ae <| by
        filter_upwards [μ.rnDeriv_self] with x hx
        rw [hx]
        simp
    _ = 1 := by simp

/-- Under `μ ≪ ν` the Hellinger affinity is the `ν`-integral of `√(dμ/dν)`. -/
lemma hellingerAffinity_eq_lintegral_rnDeriv
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    hellingerAffinity μ ν = ∫⁻ x, μ.rnDeriv ν x ^ (1 / 2 : ℝ) ∂ν := by
  rw [hellingerAffinity_eq_lintegral_rnDeriv_mul_rnDeriv hμν .rfl]
  refine lintegral_congr_ae ?_
  filter_upwards [ν.rnDeriv_self] with x hx
  rw [hx, mul_one]

/-- The density form of the Hellinger affinity:
`H(ν.withDensity f, ν) = ∫⁻ f ^ (1/2) dν`. -/
lemma hellingerAffinity_withDensity [IsFiniteMeasure ν] {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∫⁻ x, f x ∂ν ≠ ∞) :
    hellingerAffinity (ν.withDensity f) ν = ∫⁻ x, f x ^ (1 / 2 : ℝ) ∂ν := by
  haveI : IsFiniteMeasure (ν.withDensity f) := isFiniteMeasure_withDensity hf1
  rw [hellingerAffinity_eq_lintegral_rnDeriv (withDensity_absolutelyContinuous ν f)]
  refine lintegral_congr_ae ?_
  filter_upwards [ν.rnDeriv_withDensity hf] with x hx
  rw [hx]

/-- **The Hellinger affinity of two probability measures is at most `1`**, by Hölder's
inequality with exponents `p = q = 2`. -/
theorem hellingerAffinity_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    hellingerAffinity μ ν ≤ 1 := by
  have hμσ : μ ≪ μ + ν := AbsolutelyContinuous.rfl.add_right ν
  have hνσ : ν ≪ μ + ν := AbsolutelyContinuous.rfl.add_right' μ
  have ha : Measurable (μ.rnDeriv (μ + ν)) := measurable_rnDeriv _ _
  have hb : Measurable (ν.rnDeriv (μ + ν)) := measurable_rnDeriv _ _
  set F : Ω → ℝ≥0∞ := fun x => μ.rnDeriv (μ + ν) x ^ (1 / 2 : ℝ)
  set G : Ω → ℝ≥0∞ := fun x => ν.rnDeriv (μ + ν) x ^ (1 / 2 : ℝ)
  have hF : Measurable F := ENNReal.continuous_rpow_const.measurable.comp ha
  have hG : Measurable G := ENNReal.continuous_rpow_const.measurable.comp hb
  have key : hellingerAffinity μ ν = ∫⁻ x, (F * G) x ∂(μ + ν) :=
    lintegral_congr fun x =>
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsq : ∀ c : ℝ≥0∞, (c ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = c := fun c => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hF2 : ∫⁻ x, F x ^ (2 : ℝ) ∂(μ + ν) = 1 := by
    rw [lintegral_congr fun x => hsq (μ.rnDeriv (μ + ν) x),
      Measure.lintegral_rnDeriv hμσ, measure_univ]
  have hG2 : ∫⁻ x, G x ^ (2 : ℝ) ∂(μ + ν) = 1 := by
    rw [lintegral_congr fun x => hsq (ν.rnDeriv (μ + ν) x),
      Measure.lintegral_rnDeriv hνσ, measure_univ]
  calc hellingerAffinity μ ν = ∫⁻ x, (F * G) x ∂(μ + ν) := key
    _ ≤ (∫⁻ x, F x ^ (2 : ℝ) ∂(μ + ν)) ^ (1 / 2 : ℝ)
        * (∫⁻ x, G x ^ (2 : ℝ) ∂(μ + ν)) ^ (1 / 2 : ℝ) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq (μ + ν) Real.HolderConjugate.two_two
        hF.aemeasurable hG.aemeasurable
    _ = 1 := by rw [hF2, hG2]; simp

/-- **The Hellinger affinity vanishes exactly on mutually singular pairs.** -/
theorem hellingerAffinity_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerAffinity μ ν = 0 ↔ μ ⟂ₘ ν := by
  have hμσ : μ ≪ μ + ν := AbsolutelyContinuous.rfl.add_right ν
  have hνσ : ν ≪ μ + ν := AbsolutelyContinuous.rfl.add_right' μ
  have ha : Measurable (μ.rnDeriv (μ + ν)) := measurable_rnDeriv _ _
  have hb : Measurable (ν.rnDeriv (μ + ν)) := measurable_rnDeriv _ _
  have hm : Measurable fun x =>
      (μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x) ^ (1 / 2 : ℝ) :=
    ENNReal.continuous_rpow_const.measurable.comp (ha.mul hb)
  rw [hellingerAffinity, lintegral_eq_zero_iff hm]
  constructor
  · intro h0
    have hab : ∀ᵐ x ∂(μ + ν), μ.rnDeriv (μ + ν) x * ν.rnDeriv (μ + ν) x = 0 := by
      filter_upwards [h0] with x hx
      rcases ENNReal.rpow_eq_zero_iff.mp hx with ⟨h, _⟩ | ⟨_, hneg⟩
      · exact h
      · norm_num at hneg
    have hs : MeasurableSet (μ.rnDeriv (μ + ν) ⁻¹' {0}) :=
      ha (measurableSet_singleton 0)
    refine ⟨μ.rnDeriv (μ + ν) ⁻¹' {0}, hs, ?_, ?_⟩
    · -- `μ` vanishes where its density vanishes
      rw [← Measure.setLIntegral_rnDeriv' hμσ hs]
      exact setLIntegral_eq_zero hs fun x hx => hx
    · -- `ν` vanishes on the complement, since `a * b = 0` a.e. and `a ≠ 0` there
      rw [← Measure.setLIntegral_rnDeriv' hνσ hs.compl,
        lintegral_eq_zero_iff hb]
      filter_upwards [ae_restrict_of_ae hab, ae_restrict_mem hs.compl] with x hx hxc
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h (by simpa using hxc)
      · exact h
  · rintro ⟨t, ht, hμt, hνt⟩
    have hat : μ.rnDeriv (μ + ν) =ᵐ[(μ + ν).restrict t] 0 := by
      rw [← lintegral_eq_zero_iff ha, Measure.setLIntegral_rnDeriv' hμσ ht]
      exact hμt
    have hbt : ν.rnDeriv (μ + ν) =ᵐ[(μ + ν).restrict tᶜ] 0 := by
      rw [← lintegral_eq_zero_iff hb, Measure.setLIntegral_rnDeriv' hνσ ht.compl]
      exact hνt
    refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ ?_
    · filter_upwards [hat] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    · filter_upwards [hbt] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]

end Measure

end MeasureTheory
