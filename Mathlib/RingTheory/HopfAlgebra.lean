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
  mSid : (LinearMap.mul' R A) ∘ₗ (S.rTensor A) ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  midS : (LinearMap.mul' R A) ∘ₗ (S.lTensor A) ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [H : HopfAlgebra R A]

@[simp]
theorem mSid_apply (a : A) : LinearMap.mul' R A (S.rTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun mSid a

@[simp]
theorem midS_apply (a : A) : LinearMap.mul' R A (S.lTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun midS a

variable (R A)

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
  mSid := by ext; simp
  midS := by ext; simp

@[simp]
theorem antipode_apply (r : R) : antipode R R r = r := rfl

end CommSemiring
