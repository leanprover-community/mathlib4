/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

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

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

public section
namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicAt MeromorphicOn Metric Real

section FirstPart

variable {f : ℂ → ℂ} {R : ℝ}

/-!
## First Part of the First Main Theorem
-/

/--
Helper lemma for the first part of the First Main Theorem: Given a meromorphic function `f`, compute
difference between the characteristic functions of `f` and of its inverse.
-/
lemma characteristic_sub_characteristic_inv (h : Meromorphic f) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

/--
Helper lemma for the first part of the First Main Theorem: Away from zero, the difference between
the characteristic functions of `f` and `f⁻¹` equals `log ‖meromorphicTrailingCoeffAt f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_of_ne_zero
    (hf : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf, Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [MeromorphicOn.circleAverage_log_norm hR hf.meromorphicOn]
    unfold Function.locallyFinsuppWithin.logCounting
    have : (divisor f (closedBall 0 |R|)) = (divisor f Set.univ).toClosedBall R :=
      (divisor_restrict hf.meromorphicOn (by tauto)).symm
    simp [this, toClosedBall, restrictMonoidHom, restrict_apply]

/--
Helper lemma for the first part of the First Main Theorem: At 0, the difference between the
characteristic functions of `f` and `f⁻¹` equals `log ‖f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) :
    characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖ := by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h, Pi.sub_apply]
  _ = log ‖f 0‖ := by
    simp

/--
First part of the First Main Theorem, quantitative version: If `f` is meromorphic on the complex
plane, then the difference between the characteristic functions of `f` and `f⁻¹` is bounded by an
explicit constant.
-/
theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R|
      ≤ max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

/--
First part of the First Main Theorem, qualitative version: If `f` is meromorphic on the complex
plane, then the characteristic functions of `f` and `f⁻¹` agree asymptotically up to a bounded
function.
-/
theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R ↦ by simpa using characteristic_sub_characteristic_inv_le h (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

/-!
## Second Part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `⊤`) of `f` and
`f - a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : Meromorphic f) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply h.meromorphicOn.sub (MeromorphicOn.const a₀)
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
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert posLog_norm_add_le (-f θ) (a₀) using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the value `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R ↦ by simpa using abs_characteristic_sub_characteristic_shift_le h)

end SecondPart

end ValueDistribution
