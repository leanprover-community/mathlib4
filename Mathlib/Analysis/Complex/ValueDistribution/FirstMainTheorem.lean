/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section~VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section~1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Formalize the first part of the First Main Theorem, which is the more substantial part of the
  statement.
-/
namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {a₀ : E}

open Asymptotics Filter Real

/-!
## Second Part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `⊤`) of `f` and `f -
a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : MeromorphicOn f ⊤) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    circleIntegrable_posLog_norm_meromorphicOn (fun x a ↦ h x trivial)
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply circleIntegrable_posLog_norm_meromorphicOn
    apply MeromorphicOn.sub (fun x a => h x trivial) (MeromorphicOn.const a₀)
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp [abs_of_nonpos (le_of_not_ge h), neg_sub, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert posLog_norm_add_le (-f θ) (a₀) using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the value `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
theorem abs_characteristic_sub_characteristic_shift_eqO (h : MeromorphicOn f ⊤) :
    |characteristic f ⊤ - characteristic (f · - a₀) ⊤| =O[atTop] (1 : ℝ → ℝ) := by
  simp_rw [isBigO_iff', eventually_atTop]
  use log⁺ ‖a₀‖ + log 2, add_pos_of_nonneg_of_pos posLog_nonneg (log_pos one_lt_two), 0
  simp [abs_characteristic_sub_characteristic_shift_le h]

end ValueDistribution
