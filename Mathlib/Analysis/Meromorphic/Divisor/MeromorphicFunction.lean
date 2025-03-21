/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# The Divisor of a Meromorphic Function

This file defines the divisor of a meromorphic function and proves the most
basic lemmas about those divisors.

## TODO

- Compatibility with restriction of divisors/functions
- Non-negativity of the divisor for an analytic function
- Behavior under addition of functions
- Congruence lemmas for `codiscreteWithin`
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open Classical in
/-- The divisor of a meromorphic function `f`, mapping a point `z` to the order
  of `f` at `z`, and to zero if the order is infinite. -/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    DivisorOn U where
  toFun := fun z ↦ if h : MeromorphicOn f U ∧ z ∈ U then ((h.1 z h.2).order.untopD 0) else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportDiscreteWithinDomain' := by
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOf_order_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, Pi.zero_apply, dite_eq_right_iff, WithTop.untopD_eq_self_iff,
        WithTop.coe_zero]
      tauto
    · simp only [hf, false_and, ↓reduceDIte]
      exact (Eq.eventuallyEq rfl)

open Classical in
/-- Definition of the divisor -/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) :
    divisor f U z = if h : MeromorphicOn f U ∧ z ∈ U then ((h.1 z h.2).order.untopD 0) else 0 :=
  rfl

/-- Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `U` evaluates to
  `order.untopD`. -/
@[simp]
lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    divisor f U z = (hf z hz).order.untopD 0 := by simp_all [MeromorphicOn.divisor_def, hz]

/-!
## Behavior under Standard Operations
-/

/--
If orders are finite, the divisor of the scalar product of two meromorphic
functions is the sum of the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to
guarantee conditions `h₂f₁` and `h₂f₂`.
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
If orders are finite, the divisor of the product of two meromorphic
functions is the sum of the divisors.

See `MeromorphicOn.exists_order_ne_top_iff_forall` and
`MeromorphicOn.order_ne_top_of_isPreconnected` for two convenient criteria to
guarantee conditions `h₂f₁` and `h₂f₂`.
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
    by_cases ha : (h.1 z h.2).order = ⊤
    · simp [ha]
    lift (h.1 z h.2).order to ℤ using ha with a
    simp [eq_comm (a := a), neg_eq_iff_eq_neg, WithTop.untopD_eq_iff]
  · simp [divisor_def, h]

end MeromorphicOn
