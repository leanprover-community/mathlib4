/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# `LiesOver` instances for completions of number fields

This file is deprecated: use `AbsoluteValue.Completion.map` and
`AbsoluteValue.Completion.algebraOfLiesOver` instead, together with
`AbsoluteValue.Completion.algebra_eq_of_liesOver` for uniqueness of the algebra structure.
-/

deprecated_module
  "Use `AbsoluteValue.Completion.map` and `AbsoluteValue.Completion.algebraOfLiesOver`."
  (since := "2026-10-30")

public section

namespace NumberField.LiesOver

open InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L)
variable [w.LiesOver v]

@[deprecated (since := "2026-10-30")] alias completionMap := AbsoluteValue.Completion.map

@[deprecated (since := "2026-10-30")] alias continuous_completionMap :=
  AbsoluteValue.Completion.continuous_map

@[deprecated AbsoluteValue.Completion.map_coe +typeChanged (since := "2026-10-30")]
theorem completionMap_coe (x : WithAbs v.1) :
    AbsoluteValue.Completion.map v.1 w.1 (x : v.Completion) =
      ((algebraMap (WithAbs v.1) (WithAbs w.1) x : WithAbs w.1) : w.Completion) :=
  AbsoluteValue.Completion.map_coe v.1 w.1 x

/-- If `w` lies over `v`, then `w.Completion` is a `v.Completion`-algebra. -/
noncomputable scoped instance : Algebra v.Completion w.Completion :=
  AbsoluteValue.Completion.algebraOfLiesOver v.1 w.1

scoped instance : IsScalarTower K v.Completion w.Completion :=
  inferInstanceAs <| letI := AbsoluteValue.Completion.algebraOfLiesOver v.1 w.1
    IsScalarTower K v.Completion w.Completion

scoped instance : ContinuousSMul v.Completion w.Completion :=
  inferInstanceAs <| letI := AbsoluteValue.Completion.algebraOfLiesOver v.1 w.1
    ContinuousSMul v.Completion w.Completion

end NumberField.LiesOver
