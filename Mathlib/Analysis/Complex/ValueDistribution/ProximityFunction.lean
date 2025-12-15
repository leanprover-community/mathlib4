/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.CircleAverage


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

@[expose] public section

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
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity f⁻¹ ⊤` is the circle
average of `log ‖f ·‖`.
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
The proximity function of a sum of functions at `⊤` is less than or equal to the sum of the
proximity functions of the summand, plus `log` of the number of summands.
-/
theorem proximity_sum_top_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a, MeromorphicOn (f a) Set.univ) :
    proximity (∑ a ∈ s, f a) ⊤ ≤ ∑ a ∈ s, (proximity (f a) ⊤) + (fun _ ↦ log s.card) := by
  simp only [proximity_top, Finset.sum_apply]
  intro r
  have h₂f : ∀ i ∈ s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i _ ↦ circleIntegrable_posLog_norm_meromorphicOn (fun x _ ↦ hf i x trivial)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c ∈ s, f c ·‖) 0 r
    _ ≤ circleAverage (∑ c ∈ s, log⁺ ‖f c ·‖ + log s.card) 0 r := by
      apply circleAverage_mono
      · apply circleIntegrable_posLog_norm_meromorphicOn
        apply (MeromorphicOn.fun_sum (hf ·)).mono_set (by tauto)
      · apply (CircleIntegrable.fun_sum s h₂f).add (circleIntegrable_const _ _ _)
      · intro x hx
        rw [add_comm]
        apply posLog_norm_sum_le
    _ = ∑ c ∈ s, circleAverage (log⁺ ‖f c ·‖) 0 r + log s.card := by
      nth_rw 2 [← circleAverage_const (log s.card) 0 r]
      rw [← circleAverage_sum h₂f, ← circleAverage_add (CircleIntegrable.sum s h₂f)
        (circleIntegrable_const (log s.card) 0 r)]
      congr 1
      ext x
      simp

/--
The proximity function of `f + g` at `⊤` is less than or equal to the sum of the proximity functions
of `f` and `g`, plus `log 2` (where `2` is the number of summands).
-/
theorem proximity_add_top_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ + f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) + (fun _ ↦ log 2) := by
  simpa using proximity_sum_top_le Finset.univ ![f₁, f₂]
    (fun i ↦ by fin_cases i <;> assumption)

/--
The proximity function `f * g` at `⊤` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_top_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
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

@[deprecated (since := "2025-12-11")] alias proximity_top_mul_le := proximity_mul_top_le

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_zero_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    proximity (f₁ * f₂) 0 ≤ (proximity f₁ 0) + (proximity f₂ 0) := by
  calc proximity (f₁ * f₂) 0
    _ ≤ (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
      rw [← proximity_inv, mul_inv]
      apply proximity_mul_top_le (MeromorphicOn.inv_iff.mpr h₁f₁) (MeromorphicOn.inv_iff.mpr h₁f₂)
    _ = (proximity f₁ 0) + (proximity f₂ 0) := by
      rw [proximity_inv, proximity_inv]

@[deprecated (since := "2025-12-11")] alias proximity_zero_mul_le := proximity_mul_zero_le

/--
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n` times the proximity
function of `f` at `⊤`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) ⊤ = n • (proximity f ⊤) := by
  simp only [proximity, reduceDIte, Pi.pow_apply, norm_pow, posLog_pow, nsmul_eq_mul]
  ext _
  rw [Pi.mul_apply, Pi.natCast_apply, ← smul_eq_mul, ← circleAverage_fun_smul]
  rfl

/--
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n` times the proximity
function of `f` at `0`.
-/
@[simp] theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) 0 = n • (proximity f 0) := by
  rw [← proximity_inv, ← proximity_inv, (by aesop : (f ^ n)⁻¹ = f⁻¹ ^ n), proximity_pow_top]

end ValueDistribution
