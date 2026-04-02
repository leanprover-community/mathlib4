/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

public section

namespace Complex

/-- The function `tanh` is meromorphic at any `z`. -/
@[fun_prop]
theorem meromorphicAt_tanh (z : ℂ) :
    MeromorphicAt tanh z := by fun_prop [Complex.tanh]

/-- The function `tanh` is meromorphic. -/
@[fun_prop]
theorem meromorphic_tanh : Meromorphic tanh := meromorphicAt_tanh

/-- The function `tan` is meromorphic at any `z`. -/
@[fun_prop]
theorem meromorphicAt_tan (z : ℂ) :
    MeromorphicAt tan z := by fun_prop [Complex.tan]

/-- The function `tan` is meromorphic. -/
@[fun_prop]
theorem meromorphic_tan : Meromorphic tan := meromorphicAt_tan
