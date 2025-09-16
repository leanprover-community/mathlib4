/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

# Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : The `R`-linear map `A →ₗ[R] A`.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* `antipode 1 = 1` and `antipode (a * b) = antipode b * antipode a`, so in particular if `A` is
  commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf_ (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

open Bialgebra

universe u v w

/-- Isolates the antipode of a Hopf algebra, to allow API to be constructed before proving the
Hopf algebra axioms. See `HopfAlgebra` for documentation. -/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode (R) : A →ₗ[R] A

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    HopfAlgebraStruct R A where
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

export HopfAlgebraStruct (antipode)

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A] {a : A}

@[simp]
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]
theorem antipode_one :
    HopfAlgebra.antipode R (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra

lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

@[deprecated (since := "2025-05-29")]
alias sum_antipode_mul_eq := sum_antipode_mul_eq_algebraMap_counit

lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

@[deprecated (since := "2025-05-29")]
alias sum_mul_antipode_eq := sum_mul_antipode_eq_algebraMap_counit

lemma sum_antipode_mul_eq_smul (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit, Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit, Algebra.smul_def, mul_one]

@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
    _ = counit (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))

@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

end HopfAlgebra

namespace CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
theorem antipode_eq_id : antipode R (A := R) = .id := rfl

end CommSemiring
