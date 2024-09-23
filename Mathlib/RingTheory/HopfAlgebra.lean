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
* The `R`-Hopf algebra instance on the group algebra `A[G]` where `G` is a group and `A` is an
`R`-Hopf algebra: `(Add)MonoidAlgebra.instHopfAlgebra`.
* The `R`-Hopf algebra instance on `A[t, t⁻¹]` when `A` is an `R`-Hopf algebra:
`LaurentPolynomial.instHopfAlgebra`. When `A = R` this corresponds to the fact that `𝔾ₘ/R` is a
group scheme.

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
so we could deduce the facts here from an equivalence `HopfAlgebraCat R ≌ Hopf_ (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

suppress_compilation

universe u v w

/-- Isolates the antipode of a Hopf algebra, to allow API to be constructed before proving the
Hopf algebra axioms. See `HopfAlgebra` for documentation. -/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode : A →ₗ[R] A

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

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

@[simp]
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]
theorem antipode_one :
    HopfAlgebra.antipode (R := R) (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra

@[simp]
lemma sum_antipode_mul_eq {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode (R := R) (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

@[simp]
lemma sum_mul_antipode_eq {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode (R := R) (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

lemma sum_antipode_mul_eq_smul {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode (R := R) (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq, Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode (R := R) (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq, Algebra.smul_def, mul_one]

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
theorem antipode_eq_id : antipode (R := R) (A := R) = .id := rfl

end CommSemiring

namespace MonoidAlgebra

open HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type w} [Group G]

variable (R A G) in
instance instHopfAlgebraStruct : HopfAlgebraStruct R (MonoidAlgebra A G) where
  antipode := Finsupp.lsum R fun g => Finsupp.lsingle g⁻¹ ∘ₗ antipode

@[simp]
lemma antipode_single (g : G) (a : A) :
    antipode (R := R) (single g a) = single g⁻¹ (antipode (R := R) a) := by
  simp only [MonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

instance instHopfAlgebra : HopfAlgebra R (MonoidAlgebra A G) where
  mul_antipode_rTensor_comul := lhom_ext fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, comul_single,
      ← (Coalgebra.Repr.arbitrary R b).eq, map_sum,
      TensorProduct.map_tmul, lsingle_apply, LinearMap.rTensor_tmul, antipode_single,
      LinearMap.mul'_apply, single_mul_single, inv_mul_cancel, counit_single,
      Algebra.linearMap_apply, coe_algebraMap]
    simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (1 : G)),
      sum_antipode_mul_eq_smul, Algebra.algebraMap_eq_smul_one]
  mul_antipode_lTensor_comul := lhom_ext fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, comul_single,
      ← (Coalgebra.Repr.arbitrary R b).eq, map_sum, TensorProduct.map_tmul,
      lsingle_apply, LinearMap.lTensor_tmul, antipode_single, LinearMap.mul'_apply,
      single_mul_single, mul_inv_cancel, counit_single, Algebra.linearMap_apply, coe_algebraMap]
    simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (1 : G)),
      sum_mul_antipode_eq_smul, Algebra.algebraMap_eq_smul_one]

end MonoidAlgebra

namespace AddMonoidAlgebra

open HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type w} [AddGroup G]

variable (R A G) in
instance instHopfAlgebraStruct : HopfAlgebraStruct R A[G] where
  antipode := Finsupp.lsum R fun g => Finsupp.lsingle (-g) ∘ₗ antipode

@[simp]
lemma antipode_single (g : G) (a : A) :
    antipode (R := R) (single g a) = single (-g) (antipode (R := R) a) := by
  simp only [AddMonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

instance instHopfAlgebra : HopfAlgebra R A[G] where
  mul_antipode_rTensor_comul := lhom_ext fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, comul_single,
      ← (Coalgebra.Repr.arbitrary R b).eq, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.rTensor_tmul, antipode_single, LinearMap.mul'_apply, single_mul_single,
      neg_add_cancel, counit_single, Algebra.linearMap_apply, coe_algebraMap]
    simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (0 : G)),
      HopfAlgebra.sum_antipode_mul_eq_smul, Algebra.algebraMap_eq_smul_one]
  mul_antipode_lTensor_comul := lhom_ext fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, comul_single,
      ← (Coalgebra.Repr.arbitrary R b).eq, map_sum, TensorProduct.map_tmul,
      lsingle_apply, LinearMap.lTensor_tmul, antipode_single, LinearMap.mul'_apply,
      single_mul_single, add_neg_cancel, counit_single, Algebra.linearMap_apply, coe_algebraMap]
    simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (0 : G)),
      HopfAlgebra.sum_mul_antipode_eq_smul, Algebra.algebraMap_eq_smul_one]

end AddMonoidAlgebra

namespace LaurentPolynomial

open Finsupp

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

instance instHopfAlgebra : HopfAlgebra R A[T;T⁻¹] :=
  inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A ℤ)

variable {R A}

@[simp]
theorem antipode_C (a : A) :
    HopfAlgebra.antipode (R := R) (C a) = C (HopfAlgebra.antipode (R := R) a) := by
  rw [← single_eq_C, AddMonoidAlgebra.antipode_single]
  simp

@[simp]
theorem antipode_T (n : ℤ) :
    HopfAlgebra.antipode (R := R) (T (R := A) n) = T (-n) := by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]
theorem antipode_C_mul_T (a : A) (n : ℤ) :
    HopfAlgebra.antipode (R := R) (C a * T n) = C (HopfAlgebra.antipode (R := R) a) * T (-n) := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial
