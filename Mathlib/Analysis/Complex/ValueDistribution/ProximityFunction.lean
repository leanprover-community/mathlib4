/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Integral.CircleAverage


/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

open Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]
  {f g : ℂ → E} {a : WithTop E} {a₀ : E}

open Real

variable (f a) in
/--
The Proximity Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the proximity function is a
logarithmically weighted measure quantifying how well a meromorphic function `f` approximates the
constant function `a` on the circle of radius `R` in the complex plane.  In the special case where
`a = ⊤`, it quantifies how well `f` approximates infinity.
-/
noncomputable def proximity : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

/-- Expand the definition of `proximity f a₀` in case where `a₀` is finite. -/
lemma proximity_coe :
    proximity f a₀ = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a₀` in case where `a₀` is zero.
-/
lemma proximity_zero : proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0 := by
  simp [proximity]

/--
For complex-valued functions, expand the definition of `proximity f a₀` in case where `a₀` is zero.
This is a simple variant of `proximity_zero` defined above.
-/
lemma proximity_zero_of_complexValued {f : ℂ → ℂ} :
    proximity f 0 = circleAverage (log⁺ ‖f⁻¹ ·‖) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a` in case where `a₀ = ⊤`.
-/
lemma proximity_top : proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 := by
  simp [proximity]

/-!
## Elementary Properties of the Proximity Function
-/

/--
For finite values `a₀`, the proximity function `proximity f a₀` equals the proximity function for
the value zero of the shifted function `f - a₀`.
-/
lemma proximity_coe_eq_proximity_sub_const_zero :
    proximity f a₀ = proximity (f - fun _ ↦ a₀) 0 := by
  simp [proximity]

/--
For complex-valued `f`, establish a simple relation between the proximity functions of `f` and of
`f⁻¹`.
-/
theorem proximity_inv {f : ℂ → ℂ} : proximity f⁻¹ ⊤ = proximity f 0 := by
  simp [proximity_zero, proximity_top]

/--
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity
f⁻¹ ⊤` is the circle average of `log ‖f ·‖`.
-/
theorem proximity_sub_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (h₁f : MeromorphicOn f ⊤) :
    proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 := by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply circleIntegrable_posLog_norm_meromorphicOn (h₁f.mono_set (by tauto))
  · simp_rw [← norm_inv]
    apply circleIntegrable_posLog_norm_meromorphicOn (h₁f.inv.mono_set (by tauto))

/-!
## Behaviour under Arithmetic Operations
-/

/--
The proximity function `f * g` at `⊤` is less than or equal to the sum of the
proximity functions of `f` and `g`, respectively.
-/
theorem proximity_top_mul_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ * f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) := by
  calc proximity (f₁ * f₂) ⊤
  _ = circleAverage (fun x ↦ log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
    simp [proximity]
  _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
    intro r
    apply circleAverage_mono
    · simp_rw [← norm_mul]
      apply circleIntegrable_posLog_norm_meromorphicOn
      exact MeromorphicOn.fun_mul (fun x a ↦ h₁f₁ x trivial) fun x a ↦ h₁f₂ x trivial
    · apply (circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₁ x trivial)).add
        (circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₂ x trivial))
    · exact fun _ _ ↦ posLog_mul
  _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0:= by
    ext r
    apply circleAverage_add
    · exact circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₁ x trivial)
    · exact circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h₁f₂ x trivial)
  _ = (proximity f₁ ⊤) + (proximity f₂ ⊤) := rfl

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the
proximity functions of `f` and `g`, respectively.
-/
theorem proximity_zero_mul_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ * f₂) 0 ≤ (proximity f₁ 0) + (proximity f₂ 0) := by
  calc proximity (f₁ * f₂) 0
  _ ≤ (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
    rw [← proximity_inv, mul_inv]
    apply proximity_top_mul_le (MeromorphicOn.inv_iff.mpr h₁f₁) (MeromorphicOn.inv_iff.mpr h₁f₂)
  _ = (proximity f₁ 0) + (proximity f₂ 0) := by
    rw [proximity_inv, proximity_inv]

end ValueDistribution
