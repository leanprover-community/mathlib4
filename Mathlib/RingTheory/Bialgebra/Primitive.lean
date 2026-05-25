/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Primitive elements in a bialgebra

This file defines primitive elements in a bialgebra, i.e. elements `a` such that
`Δ a = a ⊗ 1 + 1 ⊗ a` and `ε a = 0`.

## Main declarations

* `IsPrimitiveElem`: Predicate for an element in a bialgebra to be primitive.
* `primitiveSubmodule`: The submodule of primitive elements.
-/

@[expose] public section

open Coalgebra Bialgebra TensorProduct

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

variable (R) in
/-- An element `a` of a bialgebra is *primitive* if `Δ a = a ⊗ 1 + 1 ⊗ a` and `ε a = 0`. -/
@[mk_iff]
structure IsPrimitiveElem (a : A) : Prop where
  /-- A primitive element `a` satisfies `Δ a = a ⊗ 1 + 1 ⊗ a`. -/
  comul_eq_tmul_one_add_one_tmul : comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a
  /-- A primitive element `a` satisfies `ε a = 0`. -/
  counit_eq_zero : counit (R := R) a = 0

attribute [simp] IsPrimitiveElem.counit_eq_zero

@[simp] lemma IsPrimitiveElem.zero : IsPrimitiveElem R (0 : A) where
  comul_eq_tmul_one_add_one_tmul := by simp
  counit_eq_zero := by simp

lemma IsPrimitiveElem.add (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a + b) where
  comul_eq_tmul_one_add_one_tmul := by
    rw [map_add, ha.comul_eq_tmul_one_add_one_tmul, hb.comul_eq_tmul_one_add_one_tmul,
      add_tmul, tmul_add]; abel
  counit_eq_zero := by simp [ha.counit_eq_zero, hb.counit_eq_zero]

lemma IsPrimitiveElem.smul (ha : IsPrimitiveElem R a) (r : R) :
    IsPrimitiveElem R (r • a) where
  comul_eq_tmul_one_add_one_tmul := by
    have h1 : r • (a ⊗ₜ[R] (1 : A)) = (r • a) ⊗ₜ[R] (1 : A) := smul_tmul' r a 1
    have h2 : r • ((1 : A) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] (r • a) := (tmul_smul r 1 a).symm
    rw [LinearMap.map_smul, ha.comul_eq_tmul_one_add_one_tmul, smul_add, h1, h2]
  counit_eq_zero := by rw [LinearMap.map_smul, ha.counit_eq_zero, smul_zero]

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
variable [CommRing R] [Ring A] [Bialgebra R A] {a : A}

lemma IsPrimitiveElem.neg (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (-a) where
  comul_eq_tmul_one_add_one_tmul := by
    rw [map_neg, ha.comul_eq_tmul_one_add_one_tmul, neg_add, neg_tmul, tmul_neg]
  counit_eq_zero := by rw [map_neg, ha.counit_eq_zero, neg_zero]

lemma IsPrimitiveElem.sub (ha : IsPrimitiveElem R a) {b : A} (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

end Ring
