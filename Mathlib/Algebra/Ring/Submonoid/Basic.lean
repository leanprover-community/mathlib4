/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Ring.Defs

/-! # Lemmas about additive closures of `Subsemigroup`. -/

open AddSubmonoid

namespace MulMemClass
variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
lemma mul_right_mem_add_closure (ha : a ∈ closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ closure (S : Set R) := by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
lemma mul_mem_add_closure (ha : a ∈ closure (S : Set R))
    (hb : b ∈ closure (S : Set R)) : a * b ∈ closure (S : Set R) := by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
lemma mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ closure (S : Set R)) :
    a * b ∈ closure (S : Set R) :=
  mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

end MulMemClass
