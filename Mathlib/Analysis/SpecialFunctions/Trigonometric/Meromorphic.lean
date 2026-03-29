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

/-- The function `Complex.tanh` is meromorphic at `z` for all `z`. -/
@[fun_prop]
public theorem meromorphicAt_tanh (z : ℂ) :
    MeromorphicAt Complex.tanh z := by fun_prop [Complex.tanh]

/-- The function `Complex.tanh` is meromorphic. -/
@[fun_prop]
public theorem meromorphic_tanh : Meromorphic Complex.tanh := meromorphicAt_tanh

/-- The function `Complex.tan` is meromorphic at `z` for all `z`. -/
@[fun_prop]
public theorem meromorphicAt_tan (z : ℂ) :
    MeromorphicAt Complex.tan z := by fun_prop [Complex.tan]

/-- The function `Complex.tan` is meromorphic. -/
@[fun_prop]
public theorem meromorphic_tan : Meromorphic Complex.tan := meromorphicAt_tan
