/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Logarithmic Derivatives of Trigonometric Functions

We compute the logarithmic derivatives of the sine and cosine functions.
-/

theorem logDeriv_sin : logDeriv (Complex.sin) = Complex.cot := by
  ext
  rw [logDeriv, Complex.deriv_sin, Pi.div_apply, Complex.cot]

theorem logDeriv_cos : logDeriv (Complex.cos) = -Complex.tan := by
  ext
  rw [logDeriv, Complex.deriv_cos', Pi.div_apply, Pi.neg_apply, Complex.tan, neg_div]
