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

open Bialgebra Coalgebra TensorProduct Algebra.TensorProduct

variable {F R A B : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B] {a b : A}

variable (R) in
/-- An element `a` of a bialgebra is *primitive* if `Δ a = a ⊗ₜ 1 + 1 ⊗ₜ a` and `ε a = 0`. -/
@[mk_iff]
structure IsPrimitiveElem (a : A) : Prop where
  counit_eq_zero : counit (R := R) a = 0
  comul_eq_tmul_add_tmul : comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a

attribute [simp] IsPrimitiveElem.counit_eq_zero IsPrimitiveElem.comul_eq_tmul_add_tmul

lemma IsPrimitiveElem.zero : IsPrimitiveElem R (0 : A) where
  counit_eq_zero := map_zero _
  comul_eq_tmul_add_tmul := by simp

lemma IsPrimitiveElem.add (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a + b) where
  counit_eq_zero := by simp [ha.counit_eq_zero, hb.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    simp [ha.comul_eq_tmul_add_tmul, hb.comul_eq_tmul_add_tmul, add_tmul, tmul_add]; abel

lemma IsPrimitiveElem.smul (ha : IsPrimitiveElem R a) (r : R) :
    IsPrimitiveElem R (r • a) where
  counit_eq_zero := by rw [map_smul, ha.counit_eq_zero, smul_zero]
  comul_eq_tmul_add_tmul := by simp [ha.comul_eq_tmul_add_tmul, smul_add, smul_tmul']

lemma IsPrimitiveElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (f a) where
  counit_eq_zero := by simp [ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_add_tmul]; simp

variable (R A) in
/-- The primitive elements form a submodule. -/
def primitiveSubmodule : Submodule R A where
  carrier := {a | IsPrimitiveElem R a}
  add_mem' := IsPrimitiveElem.add
  zero_mem' := .zero
  smul_mem' r _ ha := ha.smul r

@[simp] lemma mem_primitiveSubmodule {a : A} :
    a ∈ primitiveSubmodule R A ↔ IsPrimitiveElem R a := Iff.rfl

end Semiring

section Ring
variable [CommRing R] [Ring A] [Bialgebra R A] {a b : A}

lemma IsPrimitiveElem.neg (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (-a) where
  counit_eq_zero := by rw [map_neg, ha.counit_eq_zero, neg_zero]
  comul_eq_tmul_add_tmul := by rw [map_neg, ha.comul_eq_tmul_add_tmul, neg_add, neg_tmul, tmul_neg]

lemma IsPrimitiveElem.sub (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

/-- The commutator `[a, b] = a * b - b * a` of two primitive elements is primitive. -/
lemma IsPrimitiveElem.commutator (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a * b - b * a) where
  counit_eq_zero := by simp [ha.counit_eq_zero, hb.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    simp only [map_sub, comul_mul, ha.comul_eq_tmul_add_tmul, hb.comul_eq_tmul_add_tmul,
      add_mul, mul_add, tmul_mul_tmul, mul_one, one_mul, sub_tmul, tmul_sub]
    abel

end Ring
