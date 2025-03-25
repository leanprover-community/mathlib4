/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.LocallyFinsupp

/-!
# The Divisor of an analytic function

This file defines the divisor of an analytic function in one variable and proves the most basic
lemmas about those divisors.

## TODO

- Non-negativity of the divisor for an analytic function
- Behavior under addition of functions
- Congruence lemmas for `codiscreteWithin`
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace AnalyticOnNhd

/-!
## Definition of the Divisor
-/

open Classical in
/--
The divisor of a Analytic function `f`, mapping a point `z` to the order of `f` at `z`, and to
zero if the order is infinite.
-/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if h : AnalyticOnNhd 𝕜 f U ∧ z ∈ U then ((h.1 z h.2).order.untop₀ : ℤ) else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, dite_eq_right_iff, WithTop.untop₀_eq_zero,
      not_forall, not_or, forall_exists_index, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : AnalyticOnNhd 𝕜 f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOf_order_eq_zero_or_top] with a ha
      simp_all only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, true_and, Pi.zero_apply, dite_eq_right_iff, Nat.cast_eq_zero,
        WithTop.untop₀_eq_zero]
      tauto
    · simp only [hf, false_and, ↓reduceDIte]
      exact (Eq.eventuallyEq rfl)

open Classical in
/-- Definition of the divisor -/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) :
    divisor f U z =
      if h : AnalyticOnNhd 𝕜 f U ∧ z ∈ U then ((h.1 z h.2).order.untop₀ : ℤ) else 0 := rfl


/--
Simplifier lemma: on `U`, the divisor of a function `f` that is Analytic on `U` evaluates to
`order.untop₀`.
-/
@[simp]
lemma divisor_apply {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z ∈ U) :
    divisor f U z = (hf z hz).order.untop₀ := by simp_all [AnalyticOnNhd.divisor_def, hz]

/-!
## Behavior under Standard Operations
-/

/--
If orders are finite, the divisor of the scalar product of two Analytic functions is the sum of the
divisors.

See `AnalyticOnNhd.exists_order_ne_top_iff_forall` and
`AnalyticOnNhd.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : AnalyticOnNhd 𝕜 f₁ U)
    (h₁f₂ : AnalyticOnNhd 𝕜 f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ • f₂) U = divisor f₁ U + divisor f₂ U := by
  ext z
  by_cases hz : z ∈ U
  · lift (h₁f₁ z hz).order to ℕ using (h₂f₁ z hz) with a₁ ha₁
    lift (h₁f₂ z hz).order to ℕ using (h₂f₂ z hz) with a₂ ha₂
    simp only [h₁f₁.smul h₁f₂, hz, divisor_apply, (h₁f₁ z hz).order_smul (h₁f₂ z hz), ← ha₁, ← ha₂,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, h₁f₁, h₁f₂]
    exact rfl
  · simp [hz]

/--
If orders are finite, the divisor of the product of two Analytic functions is the sum of the
divisors.

See `AnalyticOn.exists_order_ne_top_iff_forall` and
`AnalyticOn.order_ne_top_of_isPreconnected` for two convenient criteria to guarantee conditions
`h₂f₁` and `h₂f₂`.
-/
theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : AnalyticOnNhd 𝕜 f₁ U)
    (h₁f₂ : AnalyticOnNhd 𝕜 f₂ U) (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
    (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
    divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

end AnalyticOnNhd
