/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Bolton Bailey
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.Polynomial.Degree.Definitions

instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℕ)) where
  __ : LinearOrderedAddCommMonoid (OrderDual (WithBot ℕ)) := inferInstance
  __ : Top (OrderDual (WithBot ℕ)) := inferInstance
  le_top _ := bot_le (α := WithBot ℕ)
  top_add' x := WithBot.bot_add x


noncomputable instance (R) [Semiring R] : Semiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance

noncomputable instance (R) [CommSemiring R] : CommSemiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance


def TropicallyBoundPolynomial (R) [Semiring R] : Subsemiring (Polynomial R × Tropical (OrderDual (WithBot ℕ))) where
  carrier := {p | p.1.degree ≤ OrderDual.ofDual p.2.untrop}
  mul_mem' {p q} hp hq := (p.1.degree_mul_le q.1).trans (add_le_add hp hq)
  one_mem' := Polynomial.degree_one_le
  add_mem' {p q} hp hq := (p.1.degree_add_le q.1).trans (max_le_max hp hq)
  zero_mem' := Polynomial.degree_zero.le
