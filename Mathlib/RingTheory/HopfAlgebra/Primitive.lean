/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Primitive elements in a Hopf algebra

Facts about primitive elements in a Hopf algebra.

## Main declarations

* `Bialgebra.IsPrimitiveElem.antipode_eq_neg`: the antipode sends primitive elements to their
  negation.
* `Bialgebra.IsPrimitiveElem.antipode`: the antipode preserves primitivity.

## References

* [D. Grinberg, V. Reiner, *Hopf algebras in combinatorics*][GrinbergReiner2020]
-/

public section

open Bialgebra HopfAlgebra

variable {R A : Type*} [CommSemiring R] [Ring A] [HopfAlgebra R A] {a : A}

namespace Bialgebra.IsPrimitiveElem

/-- See Proposition 1.4.17 in [GrinbergReiner2020]. -/
@[simp] theorem antipode_eq_neg (ha : IsPrimitiveElem R a) : antipode R a = -a :=
  eq_neg_of_add_eq_zero_right <| by
    simpa [ha.comul_eq_tmul_add_tmul, ha.counit_eq_zero]
      using mul_antipode_rTensor_comul_apply (R := R) a

protected lemma antipode (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (antipode R a) :=
  ha.antipode_eq_neg ▸ ha.neg

lemma antipode_antipode (ha : IsPrimitiveElem R a) : antipode R (antipode R a) = a := by
  simp [ha]

end Bialgebra.IsPrimitiveElem
