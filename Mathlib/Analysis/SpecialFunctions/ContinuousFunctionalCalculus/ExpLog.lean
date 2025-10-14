/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The exponential and logarithm based on the continuous functional calculus

This file defines the logarithm via the continuous functional calculus (CFC) and builds its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

It also shows that exponentials defined via the continuous functional calculus are equal to
`NormedSpace.exp` (defined via power series) whenever the former are not junk values.

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

## TODO

+ Show that `log (a * b) = log a + log b` whenever `a` and `b` commute (and the same for indexed
  products).
+ Relate `CFC.log` to `rpow`, `zpow`, `sqrt`, `inv`.
-/

open NormedSpace

section general_exponential
variable {𝕜 : Type*} {α : Type*} [RCLike 𝕜] [TopologicalSpace α] [CompactSpace α]

lemma NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) :
    exp 𝕜 f = (⟨exp 𝕜 ∘ f, exp_continuous.comp f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp only [NormedSpace.exp, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum]

end general_exponential

namespace CFC
section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A → Prop} [NormedRing A]
  [StarRing A] [IsTopologicalRing A] [NormedAlgebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in
lemma exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc (exp 𝕜 : 𝕜 → 𝕜) a = exp 𝕜 a := by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := (cfcHom_isClosedEmbedding (R := 𝕜) (show p a from ha)).continuous
  have _ : ContinuousOn (exp 𝕜) (spectrum 𝕜 a) := exp_continuous.continuousOn
  simp_rw [← map_exp 𝕜 _ h, cfc_apply (exp 𝕜) a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} [NormedRing A] [StarRing A]
  [IsTopologicalRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.exp a = exp ℝ a :=
  Real.exp_eq_exp_ℝ ▸ exp_eq_normedSpace_exp ha

@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma _root_.IsSelfAdjoint.exp_nonneg {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 A]
    [PartialOrder A] [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) :
    0 ≤ exp 𝕜 a := by
  rw [exp_eq_exp 𝕜 ℝ, ← real_exp_eq_normedSpace_exp]
  exact cfc_nonneg fun x _ => Real.exp_nonneg x

end RealNormed

section ComplexNormed

variable {A : Type*} {p : A → Prop} [NormedRing A] [StarRing A]
  [NormedAlgebra ℂ A] [ContinuousFunctionalCalculus ℂ A p]

lemma complex_exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc Complex.exp a = exp ℂ a :=
  Complex.exp_eq_exp_ℂ ▸ exp_eq_normedSpace_exp ha

end ComplexNormed


section real_log

open scoped ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The real logarithm, defined via the continuous functional calculus. This can be used on
matrices, operators on a Hilbert space, elements of a C⋆-algebra, etc. -/
noncomputable def log (a : A) : A := cfc Real.log a

@[simp, grind]
protected lemma _root_.IsSelfAdjoint.log {a : A} : IsSelfAdjoint (log a) := cfc_predicate _ a

@[simp, grind] lemma log_zero : log (0 : A) = 0 := by simp [log]

@[simp, grind] lemma log_one : log (1 : A) = 0 := by simp [log]

@[simp, grind =]
lemma log_algebraMap {r : ℝ} : log (algebraMap ℝ A r) = algebraMap ℝ A (Real.log r) := by
  simp [log]

lemma log_smul {r : ℝ} (a : A) (ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0) (hr : r ≠ 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) :
    log (r • a) = algebraMap ℝ A (Real.log r) + log a := by
  rw [log, ← cfc_smul_id (R := ℝ) r a, ← cfc_comp Real.log (r • ·) a, log]
  calc
    _ = cfc (fun z => Real.log r + Real.log z) a :=
      cfc_congr (Real.log_mul hr <| ha₂ · ·)
    _ = _ := by rw [cfc_const_add _ _ _]

@[grind =]
lemma log_smul' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] {r : ℝ} (a : A)
    (hr : 0 < r) (ha : IsStrictlyPositive a := by cfc_tac) :
    log (r • a) = algebraMap ℝ A (Real.log r) + log a := by
  grind [log_smul]

lemma log_pow (n : ℕ) (a : A) (ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) : log (a ^ n) = n • log a := by
  have ha₂' : ContinuousOn Real.log (spectrum ℝ a) := by fun_prop (disch := assumption)
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum ℝ a)  := by fun_prop (disch := aesop)
  rw [log, ← cfc_pow_id (R := ℝ) a n ha₁, ← cfc_comp' Real.log (· ^ n) a ha₂'', log]
  simp_rw [Real.log_pow, ← Nat.cast_smul_eq_nsmul ℝ n, cfc_const_mul (n : ℝ) Real.log a ha₂']

@[grind =]
lemma log_pow' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] (n : ℕ) (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    log (a ^ n) = n • log a := by
  grind [log_pow]

open NormedSpace in
@[grind =]
lemma log_exp (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : log (exp ℝ a) = a := by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum ℝ a) := by fun_prop (disch := simp)
  rw [log, ← real_exp_eq_normedSpace_exp, ← cfc_comp' Real.log Real.exp a hcont]
  simp [cfc_id' (R := ℝ) a]

open NormedSpace in
@[grind =]
lemma exp_log [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) : exp ℝ (log a) = a := by
  have ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0 := by grind
  rw [← real_exp_eq_normedSpace_exp .log, log, ← cfc_comp' Real.exp Real.log a (by fun_prop)]
  conv_rhs => rw [← cfc_id (R := ℝ) a]
  refine cfc_congr fun x hx => ?_
  grind [Real.exp_log]

end real_log
end CFC
