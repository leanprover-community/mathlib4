/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

See Section~VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section~1.1 of
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
## Elementary Properties of the Counting Function
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

end ValueDistribution
