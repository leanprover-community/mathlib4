/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

public section

namespace Complex

/-- The function `tan` is meromorphic in normal form on `Set.univ`. -/
theorem meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

/-- The function `tan` is meromorphic at any `z`. -/
@[fun_prop]
theorem meromorphicAt_tan (z : ℂ) : MeromorphicAt tan z :=
  (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

/-- The function `tan` is meromorphic. -/
@[fun_prop]
theorem meromorphic_tan : Meromorphic tan := meromorphicAt_tan

/-- The function `tanh` is meromorphic in normal form on `Set.univ`. -/
theorem meromorphicNFOn_tanh : MeromorphicNFOn tanh Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

/-- The function `tanh` is meromorphic at any `z`. -/
@[fun_prop]
theorem meromorphicAt_tanh (z : ℂ) : MeromorphicAt tanh z :=
  (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

/-- The function `tanh` is meromorphic. -/
@[fun_prop]
theorem meromorphic_tanh : Meromorphic tanh := meromorphicAt_tanh

end Complex
