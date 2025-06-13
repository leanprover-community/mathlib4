/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Mapping divisibility across multiplication-preserving homomorphisms

## Main definitions

* `map_dvd`

## Tags

divisibility, divides
-/

attribute [local simp] mul_assoc mul_comm mul_left_comm

variable {M N : Type*}

theorem map_dvd [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]
    (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩

theorem MulHom.map_dvd [Semigroup M] [Semigroup N] (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f

theorem MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M →* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f
