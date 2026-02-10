/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of monoid algebras

This file computes the cardinality of `R[M]` in terms of `#R` and `#M`.
-/

public section

open Cardinal Fintype

universe u v
variable (R M : Type u) (M' : Type v) [Semiring R]

namespace MonoidAlgebra

@[to_additive (attr := simp)]
lemma cardinalMk_lift_of_fintype [Fintype M'] : #R[M'] = lift.{v} #R ^ card M' := by
  simp [MonoidAlgebra]

@[to_additive]
lemma cardinalMk_of_fintype [Fintype M] : #R[M] = #R ^ card M := by simp

@[to_additive (attr := simp)]
lemma cardinalMk_lift_of_infinite [Infinite M'] [Nontrivial R] :
    #R[M'] = max (lift.{v} #R) (lift.{u} #M') := by simp [MonoidAlgebra, max_comm]

@[to_additive]
lemma cardinalMk_of_infinite [Infinite M] [Nontrivial R] : #R[M] = max #R #M := by simp

@[to_additive (attr := simp)]
lemma cardinalMk_lift_of_infinite' [Nonempty M'] [Infinite R] :
    #R[M'] = max (lift.{v} #R) (lift.{u} #M') := by simp [MonoidAlgebra, max_comm]

@[to_additive]
lemma cardinalMk_of_infinite' [Nonempty M] [Infinite R] : #R[M] = max #R #M := by simp

end MonoidAlgebra
