/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Complex.Polynomial.Basic

deprecated_module (since := "2026-01-19")

public section

namespace QuadraticForm
open QuadraticMap

@[deprecated "Use QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed"
  (since := "2026-01-19")]
theorem equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q : QuadraticForm ℂ M) (hQ : (associated (R := ℂ) Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares ℂ (1 : Fin (Module.finrank ℂ M) → ℂ)) :=
  equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]
theorem complex_equivalent {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (Q₁ Q₂ : QuadraticForm ℂ M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

end QuadraticForm
