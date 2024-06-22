/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.NormedSpace.Exponential

/-!
# The exp and log functions based on the continuous functional calculus

This file defines the log function via the continuous functional calculus and build its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

## Main declarations

+ `CFC.log`: the log function based on the CFC

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC.
-/

instance instTopologicalSemiring {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactSpace α] [NonUnitalSemiring β] [TopologicalSemiring β] :
    TopologicalSemiring C(α, β) where

instance instTopologicalRing {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactSpace α] [NonUnitalRing β] [TopologicalRing β] :
    TopologicalRing C(α, β) where

theorem tsum_apply' {α : Type*} {ι : Type*} {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    [T2Space β] {f : ι → α → β} {x : α} (hf : Summable f) :
    tsum (fun (i : ι) => f i) x = ∑' (i : ι), f i x := tsum_apply hf


namespace CFC

section exp

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

--noncomputable def real_exp (a : A) : A := cfc Real.exp a
--
--@[simp] lemma real_exp_zero [Nontrivial A] : real_exp (0 : A) = 1 := by
--  rw [← cfc_one ℝ 0, real_exp]
--  apply cfc_congr
--  rw [spectrum.zero_eq]
--  intro x hx
--  rw [Set.mem_singleton_iff] at hx
--  simp [hx]
--
--@[simp]
--lemma real_exp_algebraMap {r : ℝ} : real_exp (algebraMap ℝ A r) = algebraMap ℝ A (Real.exp r) := by
--  sorry

end exp

section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A → Prop} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [ContinuousFunctionalCalculus 𝕜 p]
  [UniqueContinuousFunctionalCalculus 𝕜 A]

-- MOVEME
open NormedSpace in
lemma exp_continuousMap_eq {α : Type*} [TopologicalSpace α] [CompactSpace α] (f : C(α, 𝕜)) :
    exp 𝕜 f = (⟨exp 𝕜 ∘ f, Continuous.comp exp_continuous f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp only [Function.comp_apply, NormedSpace.exp, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum]

open NormedSpace in
lemma exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc (exp 𝕜 : 𝕜 → 𝕜) a = exp 𝕜 a := by
  have h₁ : a = cfc (R := 𝕜) id a := by exact Eq.symm (cfc_id 𝕜 a ha)
  conv_rhs => rw [h₁, cfc_apply (id : 𝕜 → 𝕜) a ha]
  let myhom := cfcHom (R := 𝕜) (a := a) ha
  have h₃ : Continuous myhom := (cfcHom_closedEmbedding ha).continuous
  have h₄ : ContinuousOn (exp 𝕜 : 𝕜 → 𝕜) (spectrum 𝕜 a) := Continuous.continuousOn exp_continuous
  simp_rw [← map_exp 𝕜 myhom h₃, cfc_apply (exp 𝕜 : 𝕜 → 𝕜) a ha, myhom]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} {p : A → Prop} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ p]
  [UniqueContinuousFunctionalCalculus ℝ A]

open NormedSpace in
lemma real_exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc Real.exp a = exp ℝ a := by rw [Real.exp_eq_exp_ℝ]; exact exp_eq_normedSpace_exp ha

end RealNormed

section ComplexNormed

variable {A : Type*} {p : A → Prop} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℂ p]
  [UniqueContinuousFunctionalCalculus ℂ A]

open NormedSpace in
lemma complex_exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc Complex.exp a = exp ℂ a := by rw [Complex.exp_eq_exp_ℂ]; exact exp_eq_normedSpace_exp ha

end ComplexNormed


section log

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

noncomputable def log (a : A) : A := cfc Real.log a

lemma log_isSelfAdjoint {a : A} : IsSelfAdjoint (log a) := by
  sorry

lemma log_exp {a : A} (ha : IsSelfAdjoint a) : log (NormedSpace.exp ℝ a) = a := by
  unfold log
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum ℝ a) := by
    refine ContinuousOn.log (continuousOn_id' _) fun x hx => ?_
    rw [Set.mem_image] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz.2]
    exact Real.exp_ne_zero z
  have hcomp : Real.log ∘ Real.exp = id := by ext; simp
  rw [← real_exp_eq_normedSpace_exp ha, ← cfc_comp Real.log Real.exp a ha hcont]
  rw [hcomp, cfc_id (R := ℝ) a ha]

lemma exp_log {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : ContinuousOn Real.log (spectrum ℝ a)): NormedSpace.exp ℝ (log a) = a := by
  have hcont : ContinuousOn Real.exp (Real.log '' spectrum ℝ a) :=
    Continuous.continuousOn Real.continuous_exp
  have h₁ : IsSelfAdjoint (log a) := by
    unfold log

    sorry
  rw [← real_exp_eq_normedSpace_exp h₁, log, ← cfc_comp Real.exp Real.log a ha₁ hcont ha₂]
  sorry

@[simp] lemma log_one : log (1 : A) = 0 := by
  sorry

@[simp]
lemma log_algebraMap {r : ℝ} : log (algebraMap ℝ A r) = algebraMap ℝ A (Real.log r) := by
  sorry

end log

end CFC
