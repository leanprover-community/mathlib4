/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-!
# Rademacher theorem: a Lipschitz function is differentiable almost everywhere

-/

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Filter MeasureTheory Measure FiniteDimensional
open NNReal

theorem foufou {C : ℝ≥0} {f : E × ℝ → ℝ} (hf : LipschitzWith C f) {μ : Measure E} :
    ∀ᵐ p ∂(μ.prod volume), LineDifferentiableAt ℝ f p (0, 1) := by
  apply ae_prod_mem_of_ae_ae_mem (measurableSet_lineDifferentiableAt hf.continuous)
  apply eventually_of_forall (fun x ↦ ?_)
  have : ∀ᵐ (y : ℝ), DifferentiableAt ℝ (fun z ↦ f (x, z)) y := by
    apply LipschitzWith.ae_differentiableAt (C := C)
    intro z z'
    convert hf (x, z) (x, z')
    simp [Prod.edist_eq]
  filter_upwards [this] with y hy
  have h'y : DifferentiableAt ℝ (fun z ↦ f (x, z)) (y + 0) := by simpa using hy
  have : DifferentiableAt ℝ (fun t ↦ y + t) 0 :=
    (differentiable_id.const_add _).differentiableAt
  simpa only [LineDifferentiableAt, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk,
    add_zero] using h'y.comp 0 this

theorem ContinuousLinearEquiv.isAddHaarMeasure_map {E F R S : Type*} [Semiring R] [Semiring S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    [TopologicalSpace E] [TopologicalAddGroup E] [TopologicalSpace F] [T2Space F]
    [TopologicalAddGroup F]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E ≃SL[σ] F) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (μ.map L) :=
  AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

theorem doobar {C : ℝ≥0} (μ : Measure E) [IsAddHaarMeasure μ] {f : E → ℝ}
    (hf : LipschitzWith C f) (v : E) :
    ∀ᵐ p ∂μ, LineDifferentiableAt ℝ f p v := by
  rcases eq_or_ne v 0 with rfl|hv
  · simp [lineDifferentiableAt_zero]
  let n := finrank ℝ E
  let F := Fin (n-1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : (F × ℝ) ≃L[ℝ] E, L (0, 1) = v := by
    sorry /-
    have : Nontrivial E := nontrivial_of_ne v 0 hv
    have M : (F × ℝ) ≃L[ℝ] E := by
      apply ContinuousLinearEquiv.ofFinrankEq
      simpa using Nat.sub_add_cancel finrank_pos
    obtain ⟨N, hN⟩ : ∃ N : E ≃L[ℝ] E, N (M (0, 1)) = v :=
      SeparatingDual.exists_continuousLinearEquiv_apply_eq (by simp) hv
    exact ⟨M.trans N, hN⟩ -/
  have : LipschitzWith (‖(L : (F × ℝ) →L[ℝ] E)‖₊) L := L.lipschitz
  let ρ : Measure (F × ℝ) := addHaar.prod volume
  have : IsAddHaarMeasure ρ := by infer_instance
  have : ∀ᵐ p ∂ρ, LineDifferentiableAt ℝ (f ∘ L) p (0, 1) :=
    foufou (hf.comp L.lipschitz)
  have : IsAddHaarMeasure (Measure.map L ρ) := L.isAddHaarMeasure_map ρ
  have : μ ≪ Measure.map L ρ := by exact?

  sorry
