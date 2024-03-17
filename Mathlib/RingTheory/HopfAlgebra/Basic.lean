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

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

suppress_compilation

universe u v

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

variable (R A)

def MonoidAlgebra.antipode (G : Type*) [Group G] :
    MonoidAlgebra A G →ₗ[R] MonoidAlgebra A G  :=
  Finsupp.lsum R fun g => Finsupp.lsingle g⁻¹ ∘ₗ HopfAlgebra.antipode

variable {R A}

@[simp] lemma MonoidAlgebra.antipode_single {G : Type*} [Group G] (g : G) (a : A) :
    MonoidAlgebra.antipode R A G (MonoidAlgebra.single g a)
      = MonoidAlgebra.single g⁻¹ (HopfAlgebra.antipode (R := R) a) := by
  simp only [Bialgebra.ffs, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

variable (R A)

def AddMonoidAlgebra.antipode (G : Type*) [AddGroup G] :
    AddMonoidAlgebra A G →ₗ[R] AddMonoidAlgebra A G  :=
  Finsupp.lsum R fun g => Finsupp.lsingle (-g) ∘ₗ HopfAlgebra.antipode

variable {R A}

@[simp] lemma AddMonoidAlgebra.antipode_single {G : Type*} [AddGroup G] (g : G) (a : A) :
    AddMonoidAlgebra.antipode R A G (AddMonoidAlgebra.single g a)
      = AddMonoidAlgebra.single (-g) (HopfAlgebra.antipode (R := R) a) := by
  simp only [Bialgebra.ffs2, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

open scoped TensorProduct

instance MonoidAlgebra.instHopfAlgebra {A G : Type*} [Semiring A] [HopfAlgebra R A] [Group G] :
    HopfAlgebra R (MonoidAlgebra A G) where
      antipode := antipode R A G
      mul_antipode_rTensor_comul := Finsupp.lhom_ext fun g a => by
        simp_rw [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
          MonoidAlgebra.coe_algebraMap, Bialgebra.ffs, Finsupp.comul_single, Finsupp.counit_single,
          ← LinearMap.comp_apply, ← LinearMap.comp_assoc, LinearMap.rTensor_comp_map,
          antipode, Bialgebra.ffs, Finsupp.lsum_comp_lsingle, ← Bialgebra.ffs, ← LinearMap.comp_apply,
          LinearMap.mul', ← LinearMap.comp_assoc, TensorProduct.lift_comp_map,
          LinearMap.coe_comp, Function.comp_apply, ← mul_antipode_rTensor_comul_apply, Bialgebra.ffs]
        show _ = (Finsupp.lsingle (R := R) 1 ∘ₗ LinearMap.mul' _ _
          ∘ₗ LinearMap.rTensor A _) _
        congr
        ext a b : 3
        simp_rw [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, TensorProduct.lift.tmul, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Finsupp.lsingle_apply,
          ← Bialgebra.ffs, LinearMap.compl₂_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mul_apply']
        show MonoidAlgebra.single _ _ * MonoidAlgebra.single _ _ = _
        simp only [MonoidAlgebra.single_mul_single, mul_left_inv]
      mul_antipode_lTensor_comul := Finsupp.lhom_ext fun g a => by
        simp_rw [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
          MonoidAlgebra.coe_algebraMap, Bialgebra.ffs, Finsupp.comul_single, Finsupp.counit_single,
          ← LinearMap.comp_apply, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map,
          antipode, Bialgebra.ffs, Finsupp.lsum_comp_lsingle, ← Bialgebra.ffs, ← LinearMap.comp_apply,
          LinearMap.mul', ← LinearMap.comp_assoc, TensorProduct.lift_comp_map,
          LinearMap.coe_comp, Function.comp_apply, ← mul_antipode_lTensor_comul_apply, Bialgebra.ffs]
        show _ = (Finsupp.lsingle (R := R) 1 ∘ₗ LinearMap.mul' _ _
          ∘ₗ LinearMap.lTensor A _) _
        congr
        ext a b : 3
        simp_rw [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, TensorProduct.lift.tmul, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Finsupp.lsingle_apply,
          ← Bialgebra.ffs, LinearMap.compl₂_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mul_apply']
        show MonoidAlgebra.single _ _ * MonoidAlgebra.single _ _ = _
        simp only [MonoidAlgebra.single_mul_single, mul_right_inv]


@[simps! antipode] instance AddMonoidAlgebra.instHopfAlgebra {A G : Type*} [Semiring A] [HopfAlgebra R A] [AddGroup G] :
    HopfAlgebra R (AddMonoidAlgebra A G) where
      antipode := antipode R A G
      mul_antipode_rTensor_comul := Finsupp.lhom_ext fun g a => by sorry
        /-simp_rw [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply R (AddMonoidAlgebra A G),
          AddMonoidAlgebra.coe_algebraMap, Bialgebra.ffs2, Finsupp.comul_single R G A g a, Finsupp.counit_single,
          ← LinearMap.comp_apply, ← LinearMap.comp_assoc, LinearMap.rTensor_comp_map,
          antipode, Bialgebra.ffs2, Finsupp.lsum_comp_lsingle, ← Bialgebra.ffs2, ← LinearMap.comp_apply,
          LinearMap.mul', ← LinearMap.comp_assoc, TensorProduct.lift_comp_map,
          LinearMap.coe_comp, Function.comp_apply, ← mul_antipode_rTensor_comul_apply, Bialgebra.ffs2]
        show _ = (Finsupp.lsingle (R := R) 1 ∘ₗ LinearMap.mul' _ _
          ∘ₗ LinearMap.rTensor A _) _
        congr
        ext a b : 3
        simp_rw [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictScalars, TensorProduct.lift.tmul, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Finsupp.lsingle_apply,
          ← Bialgebra.ffs2, LinearMap.compl₂_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mul_apply']
        show AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = _
        simp only [AddMonoidAlgebra.single_mul_single, mul_left_inv]-/
      mul_antipode_lTensor_comul := Finsupp.lhom_ext fun g a => by sorry
        /-simp_rw [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
          AddMonoidAlgebra.coe_algebraMap, Bialgebra.ffs2, Finsupp.comul_single, Finsupp.counit_single,
          ← LinearMap.comp_apply, ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map,
          S, Bialgebra.ffs2, Finsupp.lsum_comp_lsingle, ← Bialgebra.ffs2, ← LinearMap.comp_apply,
          LinearMap.mul', ← LinearMap.comp_assoc, TensorProduct.lift_comp_map,
          LinearMap.coe_comp, Function.comp_apply, ← mul_antipode_lTensor_comul_apply, Bialgebra.ffs2]
        show _ = (Finsupp.lsingle (R := R) 1 ∘ₗ LinearMap.mul' _ _
          ∘ₗ LinearMap.lTensor A _) _
        congr
        ext a b : 3
        simp_rw [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
          LinearMap.coe_restrictantipodecalars, TensorProduct.lift.tmul, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply, Finsupp.lsingle_apply,
          ← Bialgebra.ffs2, LinearMap.compl₂_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mul_apply']
        show AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = _
        simp only [AddMonoidAlgebra.single_mul_single, mul_right_inv]-/

lemma mul'_comp_map {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B) :
    LinearMap.mul' R B ∘ₗ TensorProduct.map f.toLinearMap f.toLinearMap = f.toLinearMap ∘ₗ LinearMap.mul' R A := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LinearMap.mul'_apply, map_mul]

lemma fml {B : Type*} [Semiring B] [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B := by
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    AlgHom.toLinearMap_apply]

def ofAlgEquiv {B : Type*} [Semiring B] [Algebra R B] (f : A ≃ₐ[R] B)
    (S : B →ₗ[R] B)
    [CoalgebraStruct R B] (hcounit : Coalgebra.counit (R := R) (A := B) ∘ₗ f.toLinearEquiv
      = Coalgebra.counit (R := R) (A := A))
    (hcomul : TensorProduct.map f.toLinearEquiv f.toLinearEquiv ∘ₗ Coalgebra.comul (R := R) (A := A)
      = Coalgebra.comul (R := R) (A := B) ∘ₗ f.toLinearEquiv)
    (hS : S ∘ₗ f.toLinearEquiv = f.toLinearEquiv ∘ₗ antipode (R := R) (A := A)) :
    HopfAlgebra R B :=
{ Bialgebra.ofAlgEquiv f hcounit hcomul with
  antipode := S
  mul_antipode_rTensor_comul := by
    simp only [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 hcounit,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 hcomul]
    simp only [← LinearMap.comp_assoc, LinearMap.rTensor_comp_map, ← fml f.toAlgHom]
    simp only [LinearMap.comp_assoc, ← mul_antipode_rTensor_comul]
    simp only [← LinearMap.comp_assoc]
    congr
    ext x y
    simp only [AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearEquiv_symm,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply,
      LinearMap.mul'_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
      LinearMap.rTensor_tmul, map_mul]
    exact congr_arg (· * f y) (LinearMap.ext_iff.1 hS x)
  mul_antipode_lTensor_comul := by
    simp only [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 hcounit,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 hcomul]
    simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_map, ← fml f.toAlgHom]
    simp only [LinearMap.comp_assoc, ← mul_antipode_lTensor_comul]
    simp only [← LinearMap.comp_assoc]
    congr
    ext x y
    simp only [AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearEquiv_symm,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply,
      LinearMap.mul'_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
      LinearMap.lTensor_tmul, map_mul]
    exact congr_arg (f x * ·) (LinearMap.ext_iff.1 hS y) }

end HopfAlgebra

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
