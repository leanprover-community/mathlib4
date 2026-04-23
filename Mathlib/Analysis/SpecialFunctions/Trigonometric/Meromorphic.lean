/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

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
