/-
Copyright (c) 2026 LIU Yaohua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LIU Yaohua
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Ring.Associator

/-!
# Linearization of the commutative Jordan identity

In a commutative Jordan ring, the Jordan identity `a * b * (a * a) = a * (b * (a * a))`
can be restated as the vanishing of the associator: `associator a b (a * a) = 0`.

This file derives the standard first linearization of this identity by substituting
`a ↦ a ± c` and combining. The resulting identity expresses a relation among associators
with mixed arguments, and is a standard tool for subsequent multi-variable manipulations
(e.g. Peirce decompositions, triple product identities).

## Main results

* `IsCommJordan.four_nsmul_associator_mul_add` : the first linearization in arbitrary
  characteristic: `4 • associator a b (a * c) + 2 • associator c b (a * a) = 0`.
* `IsCommJordan.associator_mul_add` : when `A` is 2-torsion-free (`IsSMulRegular A 2`),
  this simplifies to `2 • associator a b (a * c) + associator c b (a * a) = 0`.

## References

* [McCrimmon, *A Taste of Jordan Algebras*][mccrimmon2004], Proposition 1.8.5 (JAX2')
-/

@[expose] public section

namespace IsCommJordan

variable {A : Type*} [NonUnitalNonAssocCommRing A] [IsCommJordan A]

/-- **First linearization of the commutative Jordan identity.** -/
theorem four_nsmul_associator_mul_add (a b c : A) :
    4 • associator a b (a * c) + 2 • associator c b (a * a) = 0 := by
  simp only [associator]
  have hplus := sub_eq_zero.mpr (lmul_comm_rmul_rmul (a + c) b)
  have hminus := sub_eq_zero.mpr (lmul_comm_rmul_rmul (a - c) b)
  simp only [add_mul, mul_add, sub_mul, mul_sub] at hplus hminus
  rw [mul_comm c a, lmul_comm_rmul_rmul a b, lmul_comm_rmul_rmul c b] at hplus hminus
  convert sub_eq_zero.mpr (hplus.trans hminus.symm) using 1
  abel

/-- **First linearization, simplified for 2-torsion-free rings.** -/
theorem associator_mul_add (hreg : IsSMulRegular A 2) (a b c : A) :
    2 • associator a b (a * c) + associator c b (a * a) = 0 := by
  apply hreg.right_eq_zero_of_smul
  convert four_nsmul_associator_mul_add a b c using 1
  abel

end IsCommJordan
