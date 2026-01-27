/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

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

@[expose] public section

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
`a` on the circle `∣z∣ = r`, and the logarithmic counting function, which counts the number times
that `f` attains the value `a` inside the disk `∣z∣ ≤ r`, weighted by multiplicity.
-/
noncomputable def characteristic : ℝ → ℝ := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

/--
The difference between the characteristic functions for the poles of `f` and `f - const` simplifies
to the difference between the proximity functions.
-/
@[simp]
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorphic f) (a₀ : E) :
    characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f ⊤ - proximity (f · - a₀) ⊤ := by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

/--
The characteristic function is even.
-/
theorem characteristic_even {a : WithTop E} :
    (characteristic f a).Even := proximity_even.add logCounting_even

/--
For `1 ≤ r`, the characteristic function is non-negative.
-/
theorem characteristic_nonneg {r : ℝ} {a : WithTop E} (hr : 1 ≤ r) :
    0 ≤ characteristic f a r :=
  add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

/--
The characteristic function is asymptotically non-negative.
-/
theorem characteristic_eventually_nonneg {f : ℂ → ℂ} {a : WithTop ℂ} :
    0 ≤ᶠ[Filter.atTop] characteristic f a := by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr ↦ by simp [characteristic_nonneg hr]

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of the
characteristic functions of `f` and `g`, respectively, plus `log 2` (where `2` is the number of
summands).
-/
theorem characteristic_add_top_le {f₁ f₂ : ℂ → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    characteristic (f₁ + f₂) ⊤ r ≤ characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2 := by
  simp only [characteristic]
  calc proximity (f₁ + f₂) ⊤ r + logCounting (f₁ + f₂) ⊤ r
    _ ≤ (proximity f₁ ⊤ r + proximity f₂ ⊤ r + log 2)
      + (logCounting f₁ ⊤ r + logCounting f₂ ⊤ r) := by
      gcongr
      · apply proximity_add_top_le h₁f₁ h₁f₂
      · exact logCounting_add_top_le h₁f₁ h₁f₂ hr
    _ = proximity f₁ ⊤ r + logCounting f₁ ⊤ r + (proximity f₂ ⊤ r + logCounting f₂ ⊤ r)
      + log 2 := by
      ring

/--
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of
the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_add_top_eventuallyLE {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤
      ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ ↦ log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the sum
of the characteristic functions of `f ·`, plus `log s.card`.
-/
theorem characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E) {r : ℝ}
    (hf : ∀ a, Meromorphic (f a)) (hr : 1 ≤ r) :
    characteristic (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (characteristic (f a) ⊤)) r + log s.card := by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a ∈ s, f a) ⊤ r + logCounting (∑ a ∈ s, f a) ⊤ r
  _ ≤ ((∑ a ∈ s, proximity (f a) ⊤) r) + log s.card + (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · apply logCounting_sum_top_le s f hf hr
    _ = ((∑ a ∈ s, proximity (f a) ⊤) r) + (∑ a ∈ s, (logCounting (f a) ⊤)) r + log s.card := by
      ring
    _ = ∑ x ∈ s, (proximity (f x) ⊤ r + logCounting (f x) ⊤ r) + log s.card := by
      simp [Finset.sum_add_distrib]

/--
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the
sum of the characteristic functions of `f ·`.
-/
theorem characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a, Meromorphic (f a)) :
    characteristic (∑ a ∈ s, f a) ⊤
      ≤ᶠ[Filter.atTop] ∑ a ∈ s, (characteristic (f a) ⊤) + fun _ ↦ log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_sum_top_le s f hf hr

/--
For `1 ≤ r`, the characteristic function for the zeros of `f * g` is less than or equal to the sum
of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 r ≤ (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

@[deprecated (since := "2025-12-11")] alias characteristic_zero_mul_le := characteristic_mul_zero_le

/--
Asymptotically, the characteristic function for the zeros of `f * g` is less than or equal to the
sum of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

@[deprecated (since := "2025-12-11")]
alias characteristic_zero_mul_eventually_le := characteristic_mul_zero_eventuallyLE

/--
For `1 ≤ r`, the characteristic function for the poles of `f * g` is less than or equal to the sum
of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ r ≤ (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

@[deprecated (since := "2025-12-11")] alias characteristic_top_mul_le := characteristic_mul_top_le

/--
Asymptotically, the characteristic function for the poles of `f * g` is less than or equal to the
sum of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

@[deprecated (since := "2025-12-11")]
alias characteristic_top_mul_eventually_le := characteristic_mul_top_eventuallyLE

/--
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` equals `n` times the
characteristic counting function for the zeros of `f`.
-/
@[simp]
theorem characteristic_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) 0 = n • characteristic f 0 := by
  simp_all [characteristic]

/--
For natural numbers `n`, the characteristic function for the poles of `f ^ n` equals `n` times the
characteristic function for the poles of `f`.
-/
@[simp]
theorem characteristic_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) ⊤ = n • characteristic f ⊤ := by
  simp_all [characteristic]

end ValueDistribution
