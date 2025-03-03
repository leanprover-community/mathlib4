/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Extensionality of finite measures

The main Result is `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`:
Let `A` be a StarSubalgebra of `C(E, 𝕜)` that separates points and whose elements are bounded. If
the integrals of all elements `A` with respect to two finite measures `P, P'`coincide, then the
measures coincide. In other words: If a Subalgebra separates points, it separates finite measures.
-/

open MeasureTheory Filter Real RCLike BoundedContinuousFunction

open scoped Topology

variable {E 𝕜 : Type*} [RCLike 𝕜]

/--
On a star subalgebra of bounded continuous functions, the operations "restrict scalars to ℝ"
 and "forget that a bounded continuous function is a bounded" commute..
-/
theorem restrict_toContinuousMap_eq_toContinuousMapStar_restrict [PseudoEMetricSpace E]
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} :
    ((A.restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuousBounded ℝ lipschitzWith_ofReal)).map (toContinuousMapₐ ℝ) =
    ((A.map (toContinuousMapStarₐ 𝕜)).restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuous ℝ continuous_ofReal) := by
  ext g
  simp only [Subalgebra.mem_map, Subalgebra.mem_comap, Subalgebra.mem_restrictScalars,
    StarSubalgebra.mem_toSubalgebra, toContinuousMapₐ_apply, StarSubalgebra.mem_map]
  constructor
  · intro ⟨x, hxA, hxg⟩
    use (@ofRealAm 𝕜 _).compLeftContinuousBounded ℝ lipschitzWith_ofReal x, hxA
    ext a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuousBounded_apply_apply,
      ofRealAm_coe, AlgHom.compLeftContinuous_apply_apply, algebraMap.coe_inj]
    exact DFunLike.congr_fun hxg a
  · intro ⟨x, hxA, hxg⟩
    have hg_apply (a : E) := DFunLike.congr_fun hxg a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuous_apply_apply,
      ofRealAm_coe] at hg_apply
    have h_comp_eq : (@ofRealAm 𝕜 _).compLeftContinuousBounded ℝ lipschitzWith_ofReal
        (x.comp reCLM (@reCLM 𝕜 _).lipschitz) = x := by
      ext a
      simp [hg_apply]
    use x.comp reCLM (@reCLM 𝕜 _).lipschitz
    refine ⟨by rwa [h_comp_eq], ?_⟩
    ext a
    simp [hg_apply]

namespace MeasureTheory

variable [MeasurableSpace E]

theorem ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → 𝕜) x ∂P = ∫ x, (g : E → 𝕜) x ∂P') : P = P' := by
  --consider the real subalgebra of the purely real-valued elements of A
  let A_toReal := (A.restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuousBounded ℝ lipschitzWith_ofReal)
  --the real subalgebra separates points
  have hA_toReal : (A_toReal.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
    rw [restrict_toContinuousMap_eq_toContinuousMapStar_restrict]
    exact Subalgebra.SeparatesPoints.rclike_to_real hA
  --integrals of elements of the real subalgebra wrt P, P', respectively, coincide
  have heq' : ∀ g ∈ A_toReal, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P' := by
    intro g hgA_toReal
    rw [← @ofReal_inj 𝕜, ← integral_ofReal, ← integral_ofReal]
    exact heq _ hgA_toReal
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have h0 : Tendsto (fun ε : ℝ => 6 * sqrt ε) (𝓝[>] 0) (𝓝 0) := by
    nth_rewrite 3 [← mul_zero 6]
    apply tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.const_mul 6 _)
    nth_rewrite 2 [← sqrt_zero]
    exact Continuous.tendsto continuous_sqrt 0
  have lim1 : Tendsto (fun ε => |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'|)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (eventually_nhdsWithin_of_forall (fun x _ => abs_nonneg _))
      (eventually_nhdsWithin_of_forall _) h0
    exact fun ε hε => dist_integral_mulExpNegMulSq_comp_le f hA_toReal heq' hε
  have lim2 : Tendsto (fun ε => |∫ x, mulExpNegMulSq ε (f x) ∂P
      - ∫ x, mulExpNegMulSq ε (f x) ∂P'|) (𝓝[>] 0)
      (𝓝 |∫ x, f x ∂↑P - ∫ x, f x ∂↑P'|) :=
    Tendsto.abs (Tendsto.sub (tendsto_integral_mulExpNegMulSq_comp f)
      (tendsto_integral_mulExpNegMulSq_comp f))
  exact eq_of_abs_sub_eq_zero (tendsto_nhds_unique lim2 lim1)

theorem ext_of_forall_mem_subalgebra_integral_eq_of_polish [TopologicalSpace E] [PolishSpace E]
    [BorelSpace E] {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    --{A : StarSubalgebra 𝕜 C(E, 𝕜)} (hA : A.SeparatesPoints)
    --(hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ x, (g : E → 𝕜) x ∂P = ∫ x, (g : E → 𝕜) x ∂P') : P = P' := by
  letI := upgradePolishSpace E
  exact ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA heq

end MeasureTheory
