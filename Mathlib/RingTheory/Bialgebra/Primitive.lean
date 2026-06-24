/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Primitive elements in a bialgebra

This file defines primitive elements in a bialgebra, i.e. elements `a` such that
`Δ a = a ⊗ₜ 1 + 1 ⊗ₜ a` and `ε a = 0`.

## Main declarations

* `IsPrimitiveElem R a`: `a` is a primitive element of the `R`-bialgebra.
* `primitiveSubmodule R A`: The submodule of primitive elements of `A`.

## TODO

* `primitiveSubmodule` is a `LieSubalgebra` with bracket `[a, b] = a * b - b * a`.
* In characteristic 0 over a field, the primitive elements of a cocommutative connected
  bialgebra generate it as the universal enveloping of a Lie algebra.
-/

public section

open Coalgebra TensorProduct

variable {F R A B : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B] {a b : A}

variable (R) in
/-- An element `a` of a bialgebra is *primitive* if `Δ a = a ⊗ₜ 1 + 1 ⊗ₜ a` and `ε a = 0`. -/
@[mk_iff]
structure IsPrimitiveElem (a : A) : Prop where
  /-- A primitive element `a` satisfies `ε(a) = 0`. -/
  counit_eq_zero : counit (R := R) a = 0
  /-- A primitive element `a` satisfies `Δ(a) = a ⊗ₜ 1 + 1 ⊗ₜ a`. -/
  comul_eq_tmul_add_tmul : comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a

attribute [simp] IsPrimitiveElem.counit_eq_zero IsPrimitiveElem.comul_eq_tmul_add_tmul

/-- In a bialgebra, `0` is a primitive element. -/
lemma IsPrimitiveElem.zero : IsPrimitiveElem R (0 : A) where
  counit_eq_zero := map_zero _
  comul_eq_tmul_add_tmul := by simp

/-- Primitive elements in a bialgebra are stable under addition. -/
lemma IsPrimitiveElem.add (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a + b) where
  counit_eq_zero := by simp [ha, hb]
  comul_eq_tmul_add_tmul := by simp [ha, hb, add_tmul, tmul_add]; abel

/-- Primitive elements in a bialgebra are stable under scalar multiplication. -/
lemma IsPrimitiveElem.smul (ha : IsPrimitiveElem R a) (r : R) : IsPrimitiveElem R (r • a) where
  counit_eq_zero := by simp [ha]
  comul_eq_tmul_add_tmul := by simp [ha, smul_add, smul_tmul']

/-- A bialgebra homomorphism sends primitive elements to primitive elements. -/
lemma IsPrimitiveElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (f a) where
  counit_eq_zero := by simp [ha]
  comul_eq_tmul_add_tmul := by rw [← CoalgHomClass.map_comp_comul_apply]; simp [ha]

variable (R A) in
/-- The primitive elements form a submodule. -/
def primitiveSubmodule : Submodule R A where
  carrier := {a | IsPrimitiveElem R a}
  add_mem' := .add
  zero_mem' := .zero
  smul_mem' r _ ha := ha.smul r

@[simp] lemma mem_primitiveSubmodule : a ∈ primitiveSubmodule R A ↔ IsPrimitiveElem R a := Iff.rfl

end Semiring

section Ring
variable [CommSemiring R] [Ring A] [Bialgebra R A] {a b : A}

/-- Primitive elements in a bialgebra are stable under negation. -/
lemma IsPrimitiveElem.neg (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (-a) where
  counit_eq_zero := by simpa [ha] using (map_add (counit (R := R)) (-a) a).symm
  comul_eq_tmul_add_tmul := by rw [map_neg, ha.comul_eq_tmul_add_tmul, neg_add, neg_tmul, tmul_neg]

/-- Primitive elements in a bialgebra are stable under subtraction. -/
lemma IsPrimitiveElem.sub (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a - b) := sub_eq_add_neg a b ▸ ha.add hb.neg

/-- The commutator `[a, b] = a * b - b * a` of two primitive elements is primitive. -/
lemma IsPrimitiveElem.commutator (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a * b - b * a) where
  counit_eq_zero := by simpa [ha] using (map_add (counit (R := R)) (a * b - b * a) (b * a)).symm
  comul_eq_tmul_add_tmul := by simp [ha, hb, add_mul, mul_add, sub_tmul, tmul_sub]; abel

end Ring
