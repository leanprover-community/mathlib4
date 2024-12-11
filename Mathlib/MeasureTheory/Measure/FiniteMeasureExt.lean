/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.SpecialFunctions.MulExpNegSq
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Extensionality of finite measures
The main Result is `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`:
Let `A` be a StarSubalgebra of `C(E, 𝕜)` that separates points and whose elements are bounded. If
the integrals of all elements `A` with respect to two finite measures `P, P'`coincide, then the
measures coincide. In other words: If a Subalgebra separates points, it separates finite measures.
-/

open MeasureTheory Filter

variable {E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace E]

theorem ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
    {P P' : FiniteMeasure E} {A : StarSubalgebra 𝕜 C(E, 𝕜)} (hA : A.SeparatesPoints)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → 𝕜) x ∂P = ∫ (x : E), (g : E → 𝕜) x ∂P') : P = P' := by
  --consider the real subalgebra of the purely real-valued elements of A
  let A_toReal := (A.restrictScalars ℝ).comap
      (RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal)
  --the real subalgebra separates points
  have hA_toReal : A_toReal.SeparatesPoints := Subalgebra.SeparatesPoints.rclike_to_real hA
  --elements of the real subalgebra are bounded
  have hbound_toReal : ∀ g ∈ A_toReal, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C := by
    intro g hgA_toReal
    obtain ⟨C, hboundC⟩ :=
      hbound ((RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal) g) hgA_toReal
    use C; intro x y
    specialize hboundC x y
    simp only [AlgHom.compLeftContinuous_apply_apply, RCLike.ofRealAm_coe] at hboundC
    rwa [dist_algebraMap'] at hboundC
  --integrals of elements of the real subalgebra wrt P, P', respectively, coincide
  have heq' : ∀ g ∈ A_toReal, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P' := by
    intro g hgA_toReal
    rw [← @RCLike.ofReal_inj 𝕜, ← integral_ofReal, ← integral_ofReal]
    exact heq ((RCLike.ofRealAm.compLeftContinuous ℝ RCLike.continuous_ofReal) g) hgA_toReal
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  have lim1 : Tendsto (fun ε => abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
      - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P'))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hle : ∀ᶠ ε in (nhdsWithin 0 (Set.Ioi 0)),
        abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
          - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P') ≤ 6 * ε.sqrt := by
      apply eventually_nhdsWithin_of_forall
      exact fun ε hε => dist_integral_mulExpNegMulSq_le f hA_toReal hbound_toReal heq' hε
    have g0 : Tendsto (fun ε : ℝ => 6 * ε.sqrt) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      nth_rewrite 3 [← mul_zero 6]
      apply tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.const_mul 6 _)
      nth_rewrite 2 [← Real.sqrt_zero]
      apply Continuous.tendsto Real.continuous_sqrt
    apply squeeze_zero' (eventually_nhdsWithin_of_forall (fun x _ => abs_nonneg _)) hle g0
  have lim2 : Tendsto (fun ε => abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
      - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P')) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (abs (∫ (x : E), f x ∂↑P - ∫ (x : E), f x ∂↑P'))) :=
    Tendsto.abs (Filter.Tendsto.sub (integral_mulExpNegMulSq_tendsto P f)
      (integral_mulExpNegMulSq_tendsto P' f))
  apply eq_of_abs_sub_eq_zero (tendsto_nhds_unique lim2 lim1)

theorem ext_of_forall_mem_subalgebra_integral_eq_of_polish [TopologicalSpace E] [PolishSpace E]
    [BorelSpace E] {P P' : FiniteMeasure E} {A : StarSubalgebra 𝕜 C(E, 𝕜)} (hA : A.SeparatesPoints)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → 𝕜) x ∂P = ∫ (x : E), (g : E → 𝕜) x ∂P') : P = P' := by
  letI := upgradePolishSpace E
  exact ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA hbound heq
