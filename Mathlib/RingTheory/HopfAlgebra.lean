/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* The group algebra `A[G]` where `G` is a group and `A` is a Hopf algebra:
`(Add)MonoidAlgebra.instHopfAlgebra`.
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

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

suppress_compilation

universe u v w

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode : A →ₗ[R] A
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

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

open BigOperators Coalgebra

lemma sum_antipode_mul_eq_algebraMap_counit (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, antipode (R := R) (x i) * y i = algebraMap R A (counit a) := by
  simpa [repr, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

lemma sum_mul_antipode_eq_algebraMap_counit (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, x i * antipode (R := R) (y i) = algebraMap R A (counit a) := by
  simpa [repr, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

lemma sum_antipode_mul_eq_smul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, antipode (R := R) (x i) * y i = (counit (R := R) a) • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit (repr := repr), Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i in s, x i ⊗ₜ[R] y i) :
    ∑ i in s, x i * antipode (R := R) (y i) = (counit (R := R) a) • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit (repr := repr), Algebra.smul_def, mul_one]

end HopfAlgebra

namespace MonoidAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type w} [Group G]

variable (R A G) in
/-- The antipode in the `R`-Hopf algebra structure on `MonoidAlgebra A G`, sending
`single g a` to `single g⁻¹ (antipode a)`. -/
def antipode :
    MonoidAlgebra A G →ₗ[R] MonoidAlgebra A G :=
  Finsupp.lsum R fun g => Finsupp.lsingle g⁻¹ ∘ₗ HopfAlgebra.antipode

@[simp]
lemma antipode_single (g : G) (a : A) :
    antipode R A G (single g a) = single g⁻¹ (HopfAlgebra.antipode (R := R) a) := by
  simp only [MonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

@[simps! antipode]
instance instHopfAlgebra : HopfAlgebra R (MonoidAlgebra A G) :=
  { instBialgebra R A G with
    antipode := antipode R A G
    mul_antipode_rTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.rTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, mul_left_inv, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (1 : G)),
        HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (repr := hs)]
    mul_antipode_lTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.lTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, mul_right_inv, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (1 : G)),
        HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (repr := hs)] }

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type w} [AddGroup G]

variable (R A G) in
/-- The antipode in the `R`-Hopf algebra structure on `A[G]`, sending
`single g a` to `single -g (antipode a)`. -/
def antipode : A[G] →ₗ[R] A[G] :=
  Finsupp.lsum R fun g => Finsupp.lsingle (-g) ∘ₗ HopfAlgebra.antipode

@[simp]
lemma antipode_single (g : G) (a : A) :
    antipode R A G (single g a) = single (-g) (HopfAlgebra.antipode (R := R) a) := by
  simp only [AddMonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

@[simps! antipode]
instance instHopfAlgebra : HopfAlgebra R A[G] :=
  { instBialgebra R A G with
    antipode := antipode R A G
    mul_antipode_rTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.rTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, add_left_neg, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (0 : G)),
        HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (repr := hs)]
    mul_antipode_lTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.lTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, add_right_neg, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (k := R), ← map_sum (lsingle R A (0 : G)),
        HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (repr := hs)] }

end AddMonoidAlgebra

section CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
theorem antipode_eq_id : antipode (R := R) (A := R) = .id := rfl

end CommSemiring
