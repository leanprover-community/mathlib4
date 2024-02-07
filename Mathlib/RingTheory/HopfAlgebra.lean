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

* S(1)=1 and S(ab)=S(b)S(a), so in particular if A is commutative then S is an algebra homomorphism.

* If H is commutative then S is necessarily a bijection (and I guess its square must be the
identity?)

References for these facts: Christian Kassel "Quantum Groups" (Springer GTM), around Prop III.3.1,
Theorem III.3.4 etc.

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

-/

suppress_compilation

universe u v

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with a linear
map `S` (the antipode of the Hopf algebra) satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Bialgebra R A where
  /-- The antipode of the Hopf algebra -/
  S : A →ₗ[R] A
  /-- The antipode axioms for a Hopf algebra -/
  mul_rTensor_comul :
    (LinearMap.mul' R A) ∘ₗ (S.rTensor A) ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  mul_lTensor_comul :
    (LinearMap.mul' R A) ∘ₗ (S.lTensor A) ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [H : HopfAlgebra R A]

@[simp]
theorem mul_rTensor_comul_apply (a : A) : LinearMap.mul' R A (S.rTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun mul_rTensor_comul a

@[simp]
theorem mul_lTensor_comul_apply (a : A) : LinearMap.mul' R A (S.lTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun mul_lTensor_comul a

variable (R A)

/-- `antipode R A : A →ₗ[R] A` is the antipode map on an `R`-Hopf algebra `A`. -/
def antipode : A →ₗ[R] A := HopfAlgebra.S

end HopfAlgebra

section CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
noncomputable
instance toHopfAlgebra : HopfAlgebra R R where
  S := .id
  mul_rTensor_comul := by ext; simp
  mul_lTensor_comul := by ext; simp

@[simp]
theorem antipode_apply (r : R) : antipode R R r = r := rfl

end CommSemiring
