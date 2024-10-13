/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Image of `Zsqrtd` in `ℝ`

This file defines `Zsqrtd.toReal` and related lemmas.
It is in a separate file to avoid pulling in all of `Data.Real` into `Data.Zsqrtd`.
-/


namespace Zsqrtd

/-- The image of `Zsqrtd` in `ℝ`, using `Real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `toReal h (star a)`. -/
@[simps!]
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg.mpr h)⟩

theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd

end Zsqrtd
