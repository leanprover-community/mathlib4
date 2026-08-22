/-
Copyright (c) 2023 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Multivariate polynomials and continuity

In this file we prove the following lemma:

* `MvPolynomial.continuous_eval`: `MvPolynomial.eval` is continuous

## Tags

multivariate polynomial, continuity
-/

public section

variable {X σ : Type*} [TopologicalSpace X] [CommSemiring X] [IsTopologicalSemiring X]
  (p : MvPolynomial σ X)

attribute [fun_prop] continuous_finsetSum continuous_finsetProd
theorem MvPolynomial.continuous_eval : Continuous fun x ↦ eval x p := by
  apply continuous_finsetSum -- was all just `continuity`, TODO!
  intro i a
  apply Continuous.comp' (by fun_prop)
  apply continuous_finsetProd; fun_prop
