/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : the `R`-linear map `A →ₗ[R] A`.
* `HopfAlgebra.ofConvInverse` : construct a Hopf algebra from a two-sided convolution inverse
  of the identity.
* `HopfAlgebra.ofAlgHom` : the same for commutative `A`, with `AlgHom` hypotheses.

## Main results

* `HopfAlgebra.antipode_one` : the antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : the antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* If `A` is commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

public section

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

variable {R : Type u} {A : Type v} {ι : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {a : A}

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

lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

lemma sum_antipode_mul_eq_smul (repr : Repr R a ι) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit, Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul (repr : Repr R a ι) :
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

namespace HopfAlgebra

variable {R A : Type*}

open Coalgebra WithConv LinearMap

/-- Upgrade a bialgebra to a Hopf algebra by specifying a convolution inverse of the identity. -/
noncomputable abbrev ofConvInverse [CommSemiring R] [Semiring A] [Bialgebra R A]
    (antipode : A →ₗ[R] A)
    (antipode_convMul_id : toConv antipode * toConv LinearMap.id = 1)
    (id_convMul_antipode : toConv LinearMap.id * toConv antipode = 1) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

/-- Upgrade a commutative bialgebra to a Hopf algebra by specifying the antipode `A →ₐ[R] A`
with appropriate conditions. -/
noncomputable abbrev ofAlgHom [CommSemiring R] [CommSemiring A] [Bialgebra R A]
    (antipode : A →ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ ↦ Commute.all _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ ↦ Commute.all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A :=
  ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_comul).toLinearMap))

end HopfAlgebra


namespace HopfAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

/--
If `A` is generated as an `R`-algebra by `X`, and `S : A →ₐ[R] Aᵐᵒᵖ` satisfies the two
antipode identities on `X`, then the underlying linear map gives a Hopf algebra structure on `A`.
-/
abbrev ofAntipodeOfAdjoin
    {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
    {X : Set A} (S : A →ₐ[R] Aᵐᵒᵖ)
    (hX : Algebra.adjoin R X = ⊤)
    (hxr : ∀ x ∈ X,
      LinearMap.mul' R A
        (((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).rTensor A
          (Coalgebra.comul x)) =
        algebraMap R A (Coalgebra.counit x))
    (hxl : ∀ x ∈ X,
      LinearMap.mul' R A
        (((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).lTensor A
          (Coalgebra.comul x)) =
        algebraMap R A (Coalgebra.counit x)) :
    HopfAlgebra R A where
  antipode := (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap
  mul_antipode_rTensor_comul := by
    ext t
    let P : A → Prop := fun y ↦ (LinearMap.mul' R A ∘ₗ
      LinearMap.rTensor A ((MulOpposite.opLinearEquiv (M := A) R).symm ∘ₗ S.toLinearMap) ∘ₗ
      CoalgebraStruct.comul) y = (Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit) y
    have hgood : ∀ y ∈ Algebra.adjoin R X, P y := by
      intro y hy
      apply Algebra.adjoin_induction (R := R) (s := X) (p := fun y _ => P y)
      · exact hxr
      · intro r
        simp_all only [Algebra.mem_top, LinearMap.coe_comp, Function.comp_apply,
        Algebra.linearMap_apply, comul_algebraMap, Algebra.TensorProduct.algebraMap_apply,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm,
        AlgHom.coe_toLinearMap, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        LinearMap.mul'_apply, mul_one, counit_algebraMap, P]
      · intro x y_1 hx hy_1 a a_1
        simp_all only [Algebra.mem_top, LinearMap.coe_comp, Function.comp_apply,
        Algebra.linearMap_apply, map_add, P]
      · intro x y hx hy hxP hyP
        -- `P z` in Sweedler-sum form: `∑ S'(z₍₁₎) * z₍₂₎ = ε(z)•1`
        have key : ∀ z : A, P z → (∑ i ∈ (ℛ R z).index,
            ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) ((ℛ R z).left i) *
            (ℛ R z).right i) = algebraMap R A (ε z) := fun z hz ↦ by
          unfold P at hz
          simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply] at hz
          rw [← hz, ← Coalgebra.Repr.eq (ℛ R z)]
          simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
            LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
            MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap]
        unfold P
        symm
        calc
          _ = algebraMap R A (ε x) * ∑ j ∈ (ℛ R y).index,
              ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) ((ℛ R y).left j) *
              (ℛ R y).right j := by
              rw [key y hyP]
              simp only [LinearMap.coe_comp, Function.comp_apply, counit_mul,
                linearMap_apply, map_mul]
          -- `ε(x)•1` is central, so it slides between `S'(y₍₁₎)` and `y₍₂₎`
          _ = ∑ j ∈ (ℛ R y).index,
              ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) ((ℛ R y).left j) *
              (∑ i ∈ (ℛ R x).index,
                ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) ((ℛ R x).left i) *
                (ℛ R x).right i) *
              (ℛ R y).right j := by
              rw [key x hxP, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ ↦ by rw [← mul_assoc, Algebra.commutes]
          -- recombine: `comul (x*y) = comul x * comul y` and `S` is an anti-hom
          _ = _ := by
              simp only [LinearMap.coe_comp, Function.comp_apply]
              rw [comul_mul, ← Coalgebra.Repr.eq (ℛ R x), ← Coalgebra.Repr.eq (ℛ R y),
                Finset.sum_mul_sum, Finset.sum_comm]
              simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum, LinearMap.rTensor_tmul,
                LinearMap.mul'_apply, LinearMap.coe_comp, Function.comp_apply,
                LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap,
                map_mul, MulOpposite.unop_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      · exact hy
    specialize hgood t (by rw [hX]; exact Algebra.mem_top)
    exact hgood
  mul_antipode_lTensor_comul := by
    ext t
    let P : A → Prop := fun y ↦ (LinearMap.mul' R A ∘ₗ
      LinearMap.lTensor A ((MulOpposite.opLinearEquiv (M := A) R).symm ∘ₗ S.toLinearMap) ∘ₗ
      CoalgebraStruct.comul) y = (Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit) y
    have hgood : ∀ y ∈ Algebra.adjoin R X, P y := by
      intro y hy
      apply Algebra.adjoin_induction (R := R) (s := X) (p := fun y _ => P y)
      · exact hxl
      · intro r
        simp_all only [Algebra.mem_top, LinearMap.coe_comp, Function.comp_apply,
          Algebra.linearMap_apply, comul_algebraMap, Algebra.TensorProduct.algebraMap_apply,
          LinearMap.lTensor_tmul, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm,
          AlgHom.coe_toLinearMap, map_one, MulOpposite.unop_one, LinearMap.mul'_apply,
          mul_one, counit_algebraMap, P]
      · intro x y_1 hx hy_1 a a_1
        simp_all only [Algebra.mem_top, LinearMap.coe_comp, Function.comp_apply,
          Algebra.linearMap_apply, map_add, P]
      · intro x y hx hy hxP hyP
        -- `P z` in Sweedler-sum form: `∑ z₍₁₎ * S'(z₍₂₎) = ε(z)•1`
        have key : ∀ z : A, P z → (∑ i ∈ (ℛ R z).index, (ℛ R z).left i *
            ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) ((ℛ R z).right i))
            = algebraMap R A (ε z) := fun z hz ↦ by
          unfold P at hz
          simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply] at hz
          rw [← hz, ← Coalgebra.Repr.eq (ℛ R z)]
          simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
            LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
            MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap]
        unfold P
        symm
        calc
          _ = (∑ i ∈ (ℛ R x).index, (ℛ R x).left i *
              ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)
                ((ℛ R x).right i)) *
              algebraMap R A (ε y) := by
              rw [key x hxP]
              simp only [LinearMap.coe_comp, Function.comp_apply, counit_mul,
                linearMap_apply, map_mul]
          -- `ε(y)•1` is central, so it slides between `x₍₁₎` and `S'(x₍₂₎)`
          _ = ∑ i ∈ (ℛ R x).index, (ℛ R x).left i *
              (∑ j ∈ (ℛ R y).index, (ℛ R y).left j *
                ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)
                  ((ℛ R y).right j)) *
              ((MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)
                ((ℛ R x).right i) := by
              rw [key y hyP, Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ ↦ by
                rw [mul_assoc, ← Algebra.commutes, ← mul_assoc]
          -- recombine: `comul (x*y) = comul x * comul y` and `S` is an anti-hom
          _ = _ := by
              simp only [LinearMap.coe_comp, Function.comp_apply]
              rw [comul_mul, ← Coalgebra.Repr.eq (ℛ R x), ← Coalgebra.Repr.eq (ℛ R y),
                Finset.sum_mul_sum]
              simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum, LinearMap.lTensor_tmul,
                LinearMap.mul'_apply, LinearMap.coe_comp, Function.comp_apply,
                LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap,
                map_mul, MulOpposite.unop_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      · exact hy
    specialize hgood t (by rw [hX]; exact Algebra.mem_top)
    exact hgood



end HopfAlgebra
