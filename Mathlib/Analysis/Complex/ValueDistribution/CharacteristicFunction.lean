/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.Analysis.Complex.ValueDistribution.ProximityFunction

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane.  Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

open Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a : WithTop E}

variable (f a) in
/--
The Characteristic Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the characteristic function of `f`
is defined as the sum of two terms: the proximity function, which quantifies how close `f` gets to
`a` on the circle `∣z∣ = r`, and the counting function, which counts the number times that `f`
attains the value `a` inside the disk `∣z∣ ≤ r`, weighted by multiplicity.
-/
noncomputable def characteristic : ℝ → ℝ := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

/--
The difference between the characteristic functions of `f` and `f - const` simplifies to the
difference between the proximity functions.
-/
@[simp]
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : MeromorphicOn f Set.univ)
    (a₀ : E) :
    characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f ⊤ - proximity (f · - a₀) ⊤ := by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the characteristic function of `f * g` at zero is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_zero_mul_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 r ≤ (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  have {A B C D : ℝ} : A + B + (C + D) = (A + C) + (B + D) := by ring
  rw [this]
  apply add_le_add (proximity_zero_mul_le h₁f₁ h₁f₂ r)
    (logCounting_zero_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function of `f * g` at zero is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_zero_mul_eventually_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_zero_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the characteristic function of `f * g` at `⊤` is less than or equal
to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_top_mul_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ r ≤ (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  have {A B C D : ℝ} : A + B + (C + D) = (A + C) + (B + D) := by ring
  rw [this]
  apply add_le_add (proximity_top_mul_le h₁f₁ h₁f₂ r)
    (logCounting_top_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function of `f * g` at `⊤` is less than or
equal to the sum of the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_top_mul_eventually_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z ∈ univ, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z ∈ univ, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ characteristic_top_mul_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

end ValueDistribution
