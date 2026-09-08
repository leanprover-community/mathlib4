/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Primitive elements in a bialgebra

This file collects facts about primitive elements in a bialgebra.

## Main declarations

* `Bialgebra.IsPrimitiveElem R a`: `a` is primitive, i.e. `ε a = 0` and `Δ a = 1 ⊗ₜ a + a ⊗ₜ 1`.

## TODO

* Primitive elements form a `LieSubalgebra` with bracket `[a, b] = a * b - b * a`.
  (`IsPrimitiveElem.commutator` avoids `⁅a, b⁆` so as not to import Lie theory here.)
* In characteristic 0 over a field, the primitive elements of a cocommutative connected bialgebra
  generate it as the universal enveloping of a Lie algebra. (Milnor–Moore)

## References

* [D. Grinberg, V. Reiner, *Hopf algebras in combinatorics*][GrinbergReiner2020]
-/

public section

open Coalgebra TensorProduct

variable {R A : Type*} [CommSemiring R]

namespace Bialgebra

section Semiring
variable [Semiring A] [Bialgebra R A] {a : A}

variable (R) in
/-- A primitive element of a bialgebra is a `(1, 1)`-skew-primitive element, i.e. an element `a`
such that `ε a = 0` and `Δ a = 1 ⊗ₜ a + a ⊗ₜ 1`. -/
abbrev IsPrimitiveElem (a : A) : Prop := IsSkewPrimitiveElem R 1 1 a

lemma IsPrimitiveElem.ne_one [Nontrivial R] (ha : IsPrimitiveElem R a) : a ≠ 1 :=
  ne_of_apply_ne (counit (R := R)) (by simp [ha.counit_eq_zero])

variable [IsCancelAdd A]

/-- See Proposition 1.4.17 in [GrinbergReiner2020]. -/
lemma counit_eq_zero_of_comul_eq_tmul_add_tmul (ha : comul a = 1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) :
    counit (R := R) a = 0 :=
  Coalgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul counit_one counit_one ha

lemma isPrimitiveElem_iff_comul_eq_tmul_add_tmul :
    IsPrimitiveElem R a ↔ comul a = 1 ⊗ₜ[R] a + a ⊗ₜ[R] 1 :=
  isSkewPrimitiveElem_iff_comul_eq_tmul_add_tmul counit_one counit_one

end Semiring

section Ring
variable [Ring A] [Bialgebra R A] {a b : A}

/-- The commutator `[a, b] = a * b - b * a` of two primitive elements is primitive. -/
lemma IsPrimitiveElem.commutator (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a * b - b * a) where
  counit_eq_zero := by
    simpa [ha.counit_eq_zero, hb.counit_eq_zero]
      using (map_add (counit (R := R)) (a * b - b * a) (b * a)).symm
  comul_eq_tmul_add_tmul := by
    simp [ha.comul_eq_tmul_add_tmul, hb.comul_eq_tmul_add_tmul, add_mul, mul_add, sub_tmul,
      tmul_sub]
    abel

end Ring

end Bialgebra
