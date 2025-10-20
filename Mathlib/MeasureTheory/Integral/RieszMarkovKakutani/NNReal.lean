/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Module.WeakDual
/-!
# Riesz–Markov–Kakutani representation theorem for `ℝ≥0`

This file proves the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `ℝ≥0`-linear functionals `Λ`.

## Implementation notes

The proof depends on the version of the theorem for `ℝ`-linear functional Λ because in a standard
proof one has to prove the inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.
Here we prove the result by writing `ℝ≥0`-linear `Λ` in terms of `ℝ`-linear `toRealLinear Λ` and by
reducing the statement to the `ℝ`-version of the theorem.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

namespace NNRealRMK
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (Bochner) integral of `f` (as a `ℝ`-valued function) with respect to the `rieszMeasure`
associated to `Λ` is equal to `Λ f`. -/
@[simp]
theorem integral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫ (x : X), (f x : ℝ) ∂(rieszMeasure Λ) = Λ f := by
  rw [← eq_toRealPositiveLinear_toReal Λ f,
      ← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
  simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (lower) Lebesgue integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal
to `Λ f`. -/
@[simp]
theorem lintegral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
  rw [lintegral_coe_eq_integral, ← ENNReal.ofNNReal_toNNReal]
  · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integral_nonneg (by intro a; simp)),
       NNReal.eq_iff, NNReal.coe_mk]
    exact integral_rieszMeasure Λ f
  rw [rieszMeasure]
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.comp_left f.hasCompactSupport rfl)

/-- The Riesz measure induced by a linear functional on `C_c(X, ℝ≥0)` is regular. -/
instance rieszMeasure_regular (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : (rieszMeasure Λ).Regular :=
  (rieszContent Λ).regular

section integralLinearMap

/-! We show that `NNRealRMK.rieszMeasure` is a bijection between linear functionals on `C_c(X, ℝ≥0)`
and regular measures with inverse `NNRealRMK.integralLinearMap`. -/

/-- If two regular measures give the same integral for every function in `C_c(X, ℝ≥0)`, then they
are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    (hμν : ∀ (f : C_c(X, ℝ≥0)), ∫ (x : X), (f x : ℝ) ∂μ = ∫ (x : X), (f x : ℝ) ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  repeat rw [integral_eq_integral_pos_part_sub_integral_neg_part f.integrable]
  erw [hμν f.nnrealPart, hμν (-f).nnrealPart]
  rfl

/-- If two regular measures induce the same linear functional on `C_c(X, ℝ≥0)`, then they are
equal. -/
@[simp]
theorem integralLinearMap_inj {μ ν : Measure X} [μ.Regular] [ν.Regular] :
    integralLinearMap μ = integralLinearMap ν ↔ μ = ν :=
  ⟨fun hμν ↦ Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦
      by simpa using congr(($hμν f).toReal), fun _ ↦ by congr⟩

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ≥0)`.
That is, `NNRealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
theorem rieszMeasure_integralLinearMap {μ : Measure X} [μ.Regular] :
    rieszMeasure (integralLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported_nnreal (by simp)

@[simp]
theorem integralLinearMap_rieszMeasure :
    integralLinearMap (rieszMeasure Λ) = Λ := by ext; simp

end integralLinearMap

end NNRealRMK
/-
S ⊆ P(X) is relatively compact iff tight.
Let X be a compact metric space. P(X) is a compact metric space.
-/
variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]

noncomputable section Arav

open MeasureTheory NormedSpace WeakDual CompactlySupported CompactlySupportedContinuousMap
  Filter

instance : PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure X)) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure


instance : CompactSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  let Φ := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1
    ∧ φ ⟨fun x ↦ 1, continuous_const⟩ = 1 ∧ ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f }
  have hΦ1 : CompactSpace Φ := by
    let A := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1 }
    have hA1 : IsCompact A := by
      have : A = ⇑toStrongDual ⁻¹' Metric.closedBall 0 1 := by ext x; simp [A]
      rw [this]; exact isCompact_closedBall ℝ 0 1
    let B := { φ : WeakDual ℝ C(X, ℝ) | φ ⟨(fun x => 1), continuous_const⟩ = 1 }
    let C := { φ : WeakDual ℝ C(X, ℝ) | ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f}
    have : Φ = A ∩ B ∩ C := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Φ, A, B, C]; tauto
    rw [this,←isCompact_iff_compactSpace]
    refine IsCompact.of_isClosed_subset hA1 ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · refine IsClosed.inter ?_ ?_
        · exact IsCompact.isClosed hA1
        · let phi1 : WeakDual ℝ C(X, ℝ) → ℝ := fun f ↦ f ⟨(fun x => 1), continuous_const⟩
          have : B = phi1 ⁻¹' {1} := by ext x; simp [B, phi1]
          simp only [this]
          refine (IsClosed.preimage ?_ isClosed_singleton)
          apply WeakDual.eval_continuous -- Why does this work? Can't change to exact
      · /-Maybe we can generalize this lemma to positive linear maps/order homomorphisms.-/
        have : C = ⋂ (f : { g : C_c(X, ℝ) | 0 ≤ g }), { φ : WeakDual ℝ C(X, ℝ) | 0 ≤ φ f } := by
          ext x; simp [C]
        simp only [this]; apply isClosed_iInter; intro f
        let evaluatef := fun φ : WeakDual ℝ C(X, ℝ) ↦ φ f
        have : {φ | 0 ≤ φ ↑f} = evaluatef ⁻¹' Set.Ici 0 := by ext x; simp [evaluatef]
        simp only [this]; refine (IsClosed.preimage ?_ isClosed_Ici)
        · apply WeakDual.eval_continuous
          --Why does this work? I can't change it to an exact or refine statement
    · exact fun _ h ↦ h.1.1
  apply UniformSpace.compactSpace_iff_seqCompactSpace.mpr
  constructor
  let Λ (φ : Φ) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun    := fun f => φ.1 f.1
    map_add' := by intro f g; rw [← φ.1.map_add]; rfl
    map_smul' := by intro c f; rw [← φ.1.map_smul]; rfl
    monotone' := by
      intro f g hfb; simp;
      have hφ_nonneg : 0 ≤ φ.1 ↑(g - f) := φ.2.2.2 (g - f) <| sub_nonneg.2 hfb
      have cont_map_dist : φ.1 ↑(g - f) = φ.1 (g.toContinuousMap - f.toContinuousMap) := rfl
      have : 0 ≤ φ.1 g.toContinuousMap - φ.1 f.toContinuousMap := by
        rw [← ContinuousLinearMap.map_sub, ← cont_map_dist]; exact hφ_nonneg
      simpa using (le_of_sub_nonneg this) }
  have IsPMeas (φ : Φ) : IsProbabilityMeasure <| RealRMK.rieszMeasure (Λ φ) := by
    constructor
    apply (ENNReal.toReal_eq_one_iff (RealRMK.rieszMeasure (Λ φ) Set.univ)).mp
    let c1 := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported
      ⟨(fun (x : X) => (1 : ℝ)), continuous_const⟩
    calc
      (RealRMK.rieszMeasure (Λ φ) Set.univ).toReal = (RealRMK.rieszMeasure (Λ φ)).real Set.univ := by simp [MeasureTheory.Measure.real_def]
      _ = (RealRMK.rieszMeasure (Λ φ)).real Set.univ • 1 := by simp [smul_eq_mul, mul_one]
      _ = ∫ (x : X), 1 ∂(RealRMK.rieszMeasure (Λ φ)) := (integral_const (μ := RealRMK.rieszMeasure (Λ φ)) 1).symm
      _ = Λ φ c1 := by exact (RealRMK.integral_rieszMeasure (Λ φ) c1)
      _ = φ.1 ⟨fun x ↦ 1, continuous_const⟩ := by rfl
      _ = 1 := φ.2.2.1
  have hΛ (φ : Φ) : ∀ (f : CompactlySupportedContinuousMap X ℝ), 0 ≤ f → 0 ≤ Λ φ f := φ.2.2.2
  let T : Φ → LevyProkhorov (ProbabilityMeasure X) := by--fun φ ↦ ⟨RealRMK.rieszMeasure (Λ φ), IsPMeas φ⟩
    intro φ;
    use RealRMK.rieszMeasure (Λ φ)
    exact IsPMeas φ
  have : Set.univ = Set.range T := by
    --simp [T]
    ext μ; simp only [T,Set.mem_univ, Set.mem_range, true_iff, Φ]
    let μprob : ProbabilityMeasure X := (LevyProkhorov.equiv (ProbabilityMeasure X)) μ
    let L : C_c(X, ℝ) →ₚ[ℝ] ℝ := integralPositiveLinearMap (μprob : Measure X)

    let L' : C(X,ℝ) →ₚ[ℝ] ℝ := by
      use L
    have hCcEqC : (C_c(X, ℝ) = C(X, ℝ)) := by
      sorry
    let incl : C_c(X,ℝ) →ₗ[ℝ] C(X,ℝ) := by
      refine IsLinearMap.mk' ?_ ?_
      exact fun a ↦ a.toContinuousMap
      exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }
    have : RealRMK.rieszMeasure (Λ y) = μprob := by
    -- let y_val : WeakDual ℝ C(X,ℝ) := WeakDual L
    -- let φ0_strong := (L.toContinuousLinearMap).comp incl.toContinuousLinearMap
      stop
    --use WeakDual (integralPositiveLinearMap μ)
    refine RealRMK.rieszMeasure_integralPositiveLinearMap (μ := (LevyProkhorov.equiv μ : Measure X))
    sorry /-Riesz Representation-/
  simp only [this]
  have hΦ2 : SeqCompactSpace Φ := by
    refine { isSeqCompact_univ := ?_ }
    obtain ⟨ds⟩ := hΦ1
    sorry
  apply IsSeqCompact.range
  intro s L hL
  simp [T]
  sorry

end Arav
