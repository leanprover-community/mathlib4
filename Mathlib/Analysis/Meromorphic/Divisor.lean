/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.LocallyFinsupp

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors.

## TODO

- Compatibility with restriction of divisors/functions
- Congruence lemmas for `codiscreteWithin`
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open Classical in
/--
The divisor of a meromorphic function `f`, mapping a point `z` to the order of `f` at `z`, and to
zero if the order is infinite.
-/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if h : MeromorphicOn f U ∧ z ∈ U then ((h.1 z h.2).order.untop₀) else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, dite_eq_right_iff, WithTop.untop₀_eq_zero,
      not_forall, not_or, forall_exists_index, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOf_order_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.untop₀_eq_zero,
        WithTop.coe_zero]
      tauto
    · simp only [hf, false_and, ↓reduceDIte]
      exact (Eq.eventuallyEq rfl)

open Classical in
/-- Definition of the divisor -/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) :
    divisor f U z = if h : MeromorphicOn f U ∧ z ∈ U then (h.1 z h.2).order.untop₀ else 0 :=
  rfl

/--
Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `U` evaluates to
`order.untop₀`.
-/
@[simp]
lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    divisor f U z = (hf z hz).order.untop₀ := by simp_all [MeromorphicOn.divisor_def, hz]

/-!
## Divisors of Analytic Functions
-/

/-- Analytic functions have non-negative divisors. -/
theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x ∈ U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicAt_order_nonneg]
  simp [hx]

/-!
## Behavior under Standard Operations
-/

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_smul [CompleteSpace 𝕜] {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ • f₂) U = divisor f₁ U + divisor f₂ U := by
  ext z
  by_cases hz : z ∈ U
  · lift (h₁f₁ z hz).order to ℤ using (h₂f₁ z hz) with a₁ ha₁
    lift (h₁f₂ z hz).order to ℤ using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, (h₁f₁ z hz).order_smul (h₁f₂ z hz), ← ha₁, ← ha₂,
      ← WithTop.coe_add]
  · simp [hz]

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_mul [CompleteSpace 𝕜] {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
theorem divisor_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    divisor f⁻¹ U = -divisor f U := by
  ext z
  by_cases h : MeromorphicOn f U ∧ z ∈ U
  · simp [divisor_apply, h, (h.1 z h.2).order_inv]
  · simp [divisor_def, h]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem negPart_divisor_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : AnalyticOnNhd 𝕜 f₂ U) :
    (divisor f₁ U)⁻ = (divisor (f₁ + f₂) U)⁻ := by
  ext x
  by_cases hx : x ∈ U
  · simp [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 ≤ (hf₁ x hx).order
    · simp only [Int.neg_nonpos_iff_nonneg, WithTop.untop₀_nonneg, h, sup_of_le_right,
        right_eq_sup]
      calc 0
      _ ≤ min (hf₁ x hx).order (hf₂.meromorphicOn x hx).order := by
        exact le_inf h (hf₂ x hx).meromorphicAt_order_nonneg
      _ ≤ ((hf₁.add hf₂.meromorphicOn) x hx).order := by
        exact (hf₁ x hx).order_add (hf₂ x hx).meromorphicAt
    · simp at h
      rw [(hf₁ x hx).order_add_of_order_lt_order (hf₂.meromorphicOn x hx)]
      calc (hf₁ x hx).order
      _ < 0 := h
      _ ≤ (hf₂.meromorphicOn x hx).order := (hf₂ x hx).meromorphicAt_order_nonneg
  simp [hx]

end MeromorphicOn
