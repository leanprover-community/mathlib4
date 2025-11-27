/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

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

namespace CompactlySupportedContinuousMap
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CompactSpace α] [AddCommMonoid β]

open ContinuousMap
open scoped CompactlySupported

@[simp] lemma liftCompactlySupported_zero : continuousMapEquiv (0 : C(α, β)) = 0 := rfl

variable [ContinuousAdd β]

@[simp] lemma liftCompactlySupported_add (f g : C(α, β)) :
    continuousMapEquiv (f + g) = continuousMapEquiv f + continuousMapEquiv g := rfl

end CompactlySupportedContinuousMap

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
/-!
S ⊆ P(X) is relatively compact iff tight.
Let X be a compact metric space. P(X) is a compact metric space.
-/
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]
-- Need non EMetric for LevyProkhorov.continuous_equiv_symm_probabilityMeasure
-- and T2 for RealRMK.rieszMeasure
noncomputable section Arav

open MeasureTheory NormedSpace WeakDual CompactlySupported CompactlySupportedContinuousMap
  Filter TopologicalSpace

instance : PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure X)) :=
  LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure


section SeqBA

open WeakDual TopologicalSpace Topology

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
[SeparableSpace V] (K : Set (WeakDual 𝕜 V)) [ProperSpace 𝕜] (K_cpt : IsCompact K)

theorem isSeqCompact_of_bounded_of_closed {s : Set (WeakDual 𝕜 V)}
    (hb : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsSeqCompact s := sorry

/-- The **Sequential Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in
a separable normed space `V` is a sequentially compact subset of `WeakDual 𝕜 V`. -/
theorem isSeqCompact_polar {s : Set V} (s_nhd : s ∈ 𝓝 (0 : V)) :
    IsSeqCompact (WeakDual.polar 𝕜 s) := sorry

/-- The **Sequential Banach-Alaoglu theorem**: closed balls of the dual of a separable
normed space `V` are sequentially compact in the weak-* topology. -/
theorem isSeqCompact_closedBall (x' : StrongDual 𝕜 V) (r : ℝ) :
    IsSeqCompact (toStrongDual ⁻¹' Metric.closedBall x' r) := sorry

end SeqBA

omit [BorelSpace X] in
lemma fin_integral_prob_meas {μprob : ProbabilityMeasure X} {f : C(X, ℝ)} :
    HasFiniteIntegral ⇑f ↑μprob := by
  let f' := BoundedContinuousFunction.mkOfCompact f
  obtain ⟨c, hf'⟩ := BoundedContinuousFunction.bddAbove_range_norm_comp f'
  change HasFiniteIntegral f' μprob
  simp_rw [mem_upperBounds,Set.mem_range, Function.comp_apply, forall_exists_index,
      forall_apply_eq_imp_iff] at hf'
  exact MeasureTheory.HasFiniteIntegral.of_bounded (C := c) <| Filter.Eventually.of_forall hf'

/- ### This depends on PR #31292 (the sequential Banach-Alaoglu theorem)-/

-- #info_trees in
instance : CompactSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  let Φ := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1
    ∧ φ ⟨fun x ↦ 1, continuous_const⟩ = 1 ∧ ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f }
  let A := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1 }
  have hA1 : IsCompact A := by
    have : A = ⇑toStrongDual ⁻¹' Metric.closedBall 0 1 := by ext x; simp [A]
    rw [this]; exact isCompact_closedBall ℝ 0 1
  let B := { φ : WeakDual ℝ C(X, ℝ) | φ ⟨(fun x => 1), continuous_const⟩ = 1 }
  let C := { φ : WeakDual ℝ C(X, ℝ) | ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f}
  have Φ_decomp : Φ = A ∩ B ∩ C := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Φ, A, B, C]; tauto
  have hΦ1 : CompactSpace Φ := by
    rw [Φ_decomp,←isCompact_iff_compactSpace]
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
    · exact fun _ h ↦ h.1.1
  apply UniformSpace.compactSpace_iff_seqCompactSpace.mpr
  constructor
  let Λ (φ : Φ) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun f := φ.1 f.1
    map_add' := by simp
    map_smul' := by simp
    monotone' := by
      intro f g hfb; simp
      have hφ_nonneg : 0 ≤ φ.1 ↑(g - f) := φ.2.2.2 (g - f) <| sub_nonneg.2 hfb
      have cont_map_dist : φ.1 ↑(g - f) = φ.1 (g.toContinuousMap - f.toContinuousMap) := rfl
      have : 0 ≤ φ.1 g.toContinuousMap - φ.1 f.toContinuousMap := by
        rw [← ContinuousLinearMap.map_sub, ← cont_map_dist]; exact hφ_nonneg
      simpa using (le_of_sub_nonneg this) }
  have IsPMeas (φ : Φ) : IsProbabilityMeasure <| RealRMK.rieszMeasure (Λ φ) := by
    constructor
    apply (ENNReal.toReal_eq_one_iff (RealRMK.rieszMeasure (Λ φ) Set.univ)).mp
    let c1 := CompactlySupportedContinuousMap.continuousMapEquiv
      ⟨(fun (x : X) => (1 : ℝ)), continuous_const⟩
    calc
      (RealRMK.rieszMeasure (Λ φ) Set.univ).toReal
      _ = (RealRMK.rieszMeasure (Λ φ)).real Set.univ • 1 := by
          simp [smul_eq_mul, mul_one, MeasureTheory.Measure.real_def]
      _ = ∫ (x : X), 1 ∂(RealRMK.rieszMeasure (Λ φ)) :=
          (integral_const (μ := RealRMK.rieszMeasure (Λ φ)) 1).symm
      _ = Λ φ c1 := (RealRMK.integral_rieszMeasure (Λ φ) c1)
      _ = φ.1 ⟨fun x ↦ 1, continuous_const⟩ := rfl
      _ = 1 := φ.2.2.1
  have hΛ (φ : Φ) : ∀ (f : CompactlySupportedContinuousMap X ℝ), 0 ≤ f → 0 ≤ Λ φ f := φ.2.2.2
  let T (φ : Φ) : LevyProkhorov (ProbabilityMeasure X) :=
    .ofMeasure ⟨RealRMK.rieszMeasure (Λ φ), IsPMeas φ⟩
  have : Set.univ = Set.range T := by
    ext μ; simp only [T, Set.mem_univ, Set.mem_range, true_iff, Φ]
    let μprob : ProbabilityMeasure X := LevyProkhorov.toMeasureEquiv.toFun μ
    let L : C_c(X, ℝ) →ₚ[ℝ] ℝ := integralPositiveLinearMap (μprob : Measure X)
    let liftL : C(X, ℝ) →ₚ[ℝ] ℝ :=
      { toFun := L ∘ continuousMapEquiv
        map_add' := by
          intro f g
          simp [L]
          apply MeasureTheory.integral_add' _ _
          all_goals simp [Integrable]
          · exact ⟨by measurability,fin_integral_prob_meas⟩
          constructor --I should be able to solve both goals at once with
          -- all_goals simp [Integrable] exact ⟨by measurability,fin_integral_prob_meas⟩ here, but
          -- it is reaching max heartbeats idk why??
          · simp_all only [coe_toStrongDual, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
             forall_and_index, Φ, Λ, μprob]
            apply Measurable.aestronglyMeasurable
            exact ContinuousMap.measurable g
          exact fin_integral_prob_meas
        map_smul' := by simp [L]; exact fun a b ↦ integral_const_mul a b
        monotone' := fun _ _ _ ↦ L.monotone' (by bound)}
    let φ_weak : WeakDual ℝ (C(X,ℝ)) := ((liftL).toLinearMap.mkContinuous 1 (by
      intro f; simp [-Real.norm_eq_abs,integralPositiveLinearMap_toFun, LinearMap.coe_mk,
      AddHom.coe_mk, one_mul, L, liftL]; exact BoundedContinuousFunction.norm_integral_le_norm _
          (f := (ContinuousMap.equivBoundedOfCompact X ℝ).toFun f)))
    have as_ball : φ_weak ∈ Φ := by
      simp [Φ]
      refine ⟨?_,?_,?_⟩
      · apply ContinuousLinearMap.opNorm_le_bound φ_weak (by linarith)
        intro f
        simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
          Function.comp_apply, integralPositiveLinearMap_toFun, continuousMapEquiv_apply_toFun,
          one_mul, φ_weak, L, liftL]
        exact BoundedContinuousFunction.norm_integral_le_norm μprob
            (f := (ContinuousMap.equivBoundedOfCompact X ℝ).toFun f)
      · simp [LinearMap.mkContinuous, φ_weak, L, liftL]
        change (fun f ↦ ∫ (x : X), f x ∂↑μprob) (fun x ↦ 1) = 1
        simp
      · intro g hgpos
        simp [φ_weak, L, liftL]
        change (0 ≤ (fun f ↦ ∫ (x : X), f x ∂↑μprob) g.toContinuousMap)
        simp only [coe_toContinuousMap]
        exact integral_nonneg hgpos
    let φ_fin : ↑Φ := by use φ_weak
    use φ_fin
    refine (Equiv.symm_apply_eq (LevyProkhorov.toMeasureEquiv)).mpr ?_
    apply Subtype.ext
    apply RealRMK.rieszMeasure_integralPositiveLinearMap
  simp only [this]
  have hΦ2 : SeqCompactSpace Φ := by --Jannette's Project (Seq. banach alaoglu thm)
    --obtain ⟨ds⟩ := hΦ1
    refine (seqCompactSpace_iff ↑Φ).mpr ?_
    -- rw [Φ_decomp]
    refine FirstCountableTopology.seq_compact_of_compact (X := )
    apply IsCompact.isSeqCompact h
    have Sep : SeparableSpace C(X, ℝ) := sorry
    refine isSeqCompact_of_bounded_of_closed ?_ ?_ (𝕜 := ℝ) (V := C(X, ℝ)) (s := Φ)
    sorry
  apply IsSeqCompact.range
  refine Continuous.seqContinuous ?_
  simp [T]
  let f : ↑Φ → Measure X := fun φ => RealRMK.rieszMeasure (Λ φ)
  refine Continuous.comp ?_ ?_ (Y := ProbabilityMeasure X)
  · exact LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  · rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
    intro func
    let funk := CompactlySupportedContinuousMap.continuousMapEquiv func.toContinuousMap
    have what (x) : ∫ (x : X), func x ∂RealRMK.rieszMeasure (Λ x) =
        (Λ x) (continuousMapEquiv func.toContinuousMap) := RealRMK.integral_rieszMeasure (Λ x) funk
    simp [what, Λ]
    exact Continuous.comp (WeakDual.eval_continuous _)
        continuous_subtype_val (g := (fun (x : WeakDual ℝ C(X,ℝ)) ↦ x func.toContinuousMap))


end Arav
