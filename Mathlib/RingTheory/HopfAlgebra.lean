/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.Bialgebra

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

# Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode R A` : The `R`-linear map `A →ₗ[R] A`

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
agree then the antipodes must also agree).

* `S 1 = 1` and `S (a * b) = S b * S a`, so in particular if A is commutative then S is an
  algebra homomorphism.

* If H is commutative then S is necessarily a bijection (and I guess its square must be the
identity?)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>
* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

suppress_compilation

universe u v

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with a linear
map `S` (the antipode of the Hopf algebra) satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Bialgebra R A where
  /-- The antipode of the Hopf algebra -/
  antipode : A →ₗ[R] A
  /-- The antipode axioms for a Hopf algebra -/
  mul_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  mul_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

@[simp]
theorem mul_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_rTensor_comul a

@[simp]
theorem mul_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_lTensor_comul a

end HopfAlgebra

section CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
noncomputable
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_rTensor_comul := by ext; simp
  mul_lTensor_comul := by ext; simp

@[simp]
theorem antipode_eq_id : antipode (R := R) (A := R) = .id := rfl

end CommSemiring
