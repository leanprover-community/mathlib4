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

It also shows that exponentials defined via the CFC are equal to `NormedSpace.exp` (defined via
power series) whenever the former are not junk values.

## Main declarations

+ `CFC.log`: the real log function based on the CFC, i.e. `cfc Real.log`
+ `CFC.exp_eq_normedSpace_exp`: exponentials based on the CFC are equal to exponentials based
  on power series.
+ `CFC.log_exp` and `CFC.exp_log`: `CFC.log` and `NormedSpace.exp ℝ` are inverses of each other.

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC. In particular, we don't give separate
definitions for them.
-/

open NormedSpace

section general_exponential
variable {𝕜 : Type*} {α : Type*} [RCLike 𝕜] [TopologicalSpace α] [CompactSpace α]

lemma NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) :
    exp 𝕜 f = (⟨exp 𝕜 ∘ f, Continuous.comp exp_continuous f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp only [Function.comp_apply, NormedSpace.exp, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum]

end general_exponential

namespace CFC
section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A → Prop} [PartialOrder A] [NormedRing A]
  [StarRing A] [StarOrderedRing A] [TopologicalRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [ContinuousFunctionalCalculus 𝕜 p]
  [UniqueContinuousFunctionalCalculus 𝕜 A]

lemma exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc (exp 𝕜 : 𝕜 → 𝕜) a = exp 𝕜 a := by
  have h₁ : a = cfc (R := 𝕜) id a := (cfc_id 𝕜 a ha).symm
  conv_rhs => rw [h₁, cfc_apply id a ha]
  let φ := cfcHom (R := 𝕜) ha
  have h₂ : Continuous φ := (cfcHom_closedEmbedding ha).continuous
  have _ : ContinuousOn (exp 𝕜) (spectrum 𝕜 a) := Continuous.continuousOn exp_continuous
  simp_rw [← map_exp 𝕜 φ h₂, cfc_apply (exp 𝕜) a ha, φ]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} {p : A → Prop} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ p]
  [UniqueContinuousFunctionalCalculus ℝ A]

lemma real_exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc Real.exp a = exp ℝ a := by rw [Real.exp_eq_exp_ℝ]; exact exp_eq_normedSpace_exp ha

end RealNormed

section ComplexNormed

variable {A : Type*} {p : A → Prop} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℂ p]
  [UniqueContinuousFunctionalCalculus ℂ A]

lemma complex_exp_eq_normedSpace_exp {a : A} (ha : p a) :
    cfc Complex.exp a = exp ℂ a := by rw [Complex.exp_eq_exp_ℂ]; exact exp_eq_normedSpace_exp ha

end ComplexNormed


section real_log

open scoped ComplexOrder

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

noncomputable def log (a : A) : A := cfc Real.log a

lemma isSelfAdjoint_log {a : A} : IsSelfAdjoint (log a) := cfc_predicate _ a

lemma log_exp {a : A} (ha : IsSelfAdjoint a) : log (NormedSpace.exp ℝ a) = a := by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum ℝ a) := by
    refine ContinuousOn.log (continuousOn_id' _) fun x hx => ?_
    rw [Set.mem_image] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz.2]
    exact Real.exp_ne_zero z
  have hcomp : Real.log ∘ Real.exp = id := by ext; simp
  rw [log, ← real_exp_eq_normedSpace_exp ha, ← cfc_comp Real.log Real.exp a ha hcont]
  rw [hcomp, cfc_id (R := ℝ) a ha]

-- TODO: Relate the hypothesis to a notion of strict positivity
lemma exp_log {a : A} (ha₁ : IsSelfAdjoint a := by cfc_tac) (ha₂ : ∀ x ∈ spectrum ℝ a, 0 < x) :
    NormedSpace.exp ℝ (log a) = a := by
  have ha₃ : ContinuousOn Real.log (spectrum ℝ a) := by
    refine ContinuousOn.mono Real.continuousOn_log fun x hx => ?_
    rw [Set.mem_compl_singleton_iff]
    exact ne_of_gt <| ha₂ x hx
  have hcont : ContinuousOn Real.exp (Real.log '' spectrum ℝ a) := by fun_prop
  rw [← real_exp_eq_normedSpace_exp isSelfAdjoint_log,
      log, ← cfc_comp Real.exp Real.log a ha₁ hcont ha₃]
  conv_rhs => rw [← cfc_id (R := ℝ) a ha₁]
  refine cfc_congr ?_
  intro x hx
  simp only [Function.comp_apply, Real.exp_log (ha₂ x hx), id_eq]

@[simp] lemma log_zero : log (0 : A) = 0 := by simp [log]

@[simp] lemma log_one : log (1 : A) = 0 := by simp [log]

@[simp]
lemma log_algebraMap {r : ℝ} : log (algebraMap ℝ A r) = algebraMap ℝ A (Real.log r) := by
  simp [log]

-- TODO: Relate the hypothesis to a notion of strict positivity
lemma log_smul {r : ℝ} {a : A} (ha₁ : IsSelfAdjoint a := by cfc_tac)
    (ha₂ : ∀ x ∈ spectrum ℝ a, 0 < x) (hr : 0 < r) :
    log (r • a) = algebraMap ℝ A (Real.log r) + log a := by
  have ha₂' : ContinuousOn Real.log (spectrum ℝ a)  := by
    refine ContinuousOn.mono Real.continuousOn_log fun x hx => ?_
    rw [Set.mem_compl_singleton_iff]
    exact ne_of_gt (ha₂ x hx)
  have ha₂'' : ContinuousOn Real.log ((r • ·) '' spectrum ℝ a)  := by
    refine ContinuousOn.mono Real.continuousOn_log fun x hx => ?_
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_image] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz.2]
    have : 0 < r • z := (smul_pos_iff_of_pos_left hr).mpr (ha₂ z hz.1)
    exact ne_of_gt this
  rw [log, ← cfc_smul_id (S := ℝ) (R := ℝ) r a ha₁, ← cfc_comp Real.log (r • ·) a ha₁ ha₂'', log]
  have hmain : Set.EqOn (Real.log ∘ (r • ·)) (fun z => Real.log r + Real.log z) (spectrum ℝ a) := by
    intro x hx
    simp only [smul_eq_mul, Function.comp_apply]
    exact Real.log_mul (ne_of_gt hr) <| ne_of_gt (ha₂ x hx)
  rw [cfc_congr hmain, cfc_const_add _ a _ ha₁ ha₂']

-- TODO: Relate the hypothesis to a notion of strict positivity
lemma log_pow {n : ℕ} {a : A} (ha₁ : IsSelfAdjoint a := by cfc_tac)
    (ha₂ : ∀ x ∈ spectrum ℝ a, 0 < x) : log (a ^ n) = n • log a := by
  have ha₂' : ContinuousOn Real.log (spectrum ℝ a) := by
    refine ContinuousOn.mono Real.continuousOn_log fun x hx => ?_
    rw [Set.mem_compl_singleton_iff]
    exact ne_of_gt (ha₂ x hx)
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum ℝ a)  := by
    refine ContinuousOn.mono Real.continuousOn_log fun x hx => ?_
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_image] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz.2]
    exact ne_of_gt (pow_pos (ha₂ z hz.1) n)
  rw [log, ← cfc_pow_id (R := ℝ) a n ha₁, ← cfc_comp Real.log (· ^ n) a ha₁ ha₂'', log]
  have hmain : Real.log ∘ (· ^ n) = fun z => n • Real.log z := by ext; simp
  rw [hmain, cfc_smul n Real.log a ha₂']

end real_log
end CFC
