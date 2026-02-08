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
* `HopfAlgebra.antipode` : The `R`-linear map `A →ₗ[R] A`.

## Main results

* `HopfAlgebra.antipode_one` : The antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : The antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.

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

@[expose] public section

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

lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

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

/-! ### The antipode is an antihomomorphism

We prove that `antipode (a * b) = antipode b * antipode a`. The proof uses the "left inverse
equals right inverse" trick in the convolution algebra `(A ⊗ A) →ₗ[R] A`.
-/

open scoped ConvolutionProduct TensorProduct

/-- The antipode reverses multiplication: `S(ab) = S(b)S(a)`. -/
theorem antipode_mul (a b : A) :
    antipode R (a * b) = antipode R b * antipode R a := by
  -- We show that the linear maps S ∘ μ and μ ∘ (S ⊗ S) ∘ comm are equal,
  -- by proving they are both convolution inverses of μ.
  suffices h : antipode R ∘ₗ LinearMap.mul' R A =
      LinearMap.mul' R A ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ
        TensorProduct.comm R A A by
    exact congr(($h) (a ⊗ₜ b))
  apply left_inv_eq_right_inv (a := LinearMap.mul' R A)
  · -- Left inverse: (S ∘ μ) * μ = 1
    refine TensorProduct.ext' fun x y => ?_
    -- Unfold convolution product: (f * g)(x ⊗ y) = μ(f ⊗ g)(Δ(x ⊗ y))
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    -- The coalgebra on A ⊗ A: Δ(x ⊗ y) = σ (Δx ⊗ Δy) where σ = tensorTensorTensorComm
    rw [TensorProduct.comul_tmul]
    -- Use Sweedler representations for x and y
    let ℛx := ℛ R x; let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    -- Goal: ∑ S(x₁y₁) * (x₂y₂) = algebraMap (ε(x)ε(y))
    -- The counit on A ⊗ A: ε(x ⊗ y) = ε(y) • ε(x) = ε(x)ε(y) since R is commutative
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    -- Use the bialgebra comultiplication axiom: Δ(xy) = Δ(x)Δ(y)
    have key := mul_antipode_rTensor_comul_apply (R := R) (x * y)
    rw [Bialgebra.comul_mul, ← ℛx.eq, ← ℛy.eq] at key
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Bialgebra.counit_mul] at key
    rw [Finset.sum_comm] at key
    simp only [Algebra.algebraMap_eq_smul_one] at key
    rw [mul_comm (counit (R := R) x) (counit y)] at key
    exact key
  · -- Right inverse: μ * (μ ∘ (S ⊗ S) ∘ comm) = 1
    refine TensorProduct.ext' fun x y => ?_
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    rw [TensorProduct.comul_tmul]
    let ℛx := ℛ R x; let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    -- Goal: ∑ (x₁y₁) * S(y₂)S(x₂) = ε(x)ε(y) • 1
    -- Rearrange the sum using antipode axioms
    calc ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
        (ℛx.left i * ℛy.left j) * (antipode R (ℛy.right j) * antipode R (ℛx.right i))
      _ = ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
          ℛx.left i * (ℛy.left j * antipode R (ℛy.right j) * antipode R (ℛx.right i)) := by
        simp only [mul_assoc]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          ((∑ j ∈ ℛy.index, ℛy.left j * antipode R (ℛy.right j)) * antipode R (ℛx.right i)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (counit (R := R) y • (1 : A) * antipode R (ℛx.right i)) := by
        rw [sum_mul_antipode_eq_smul ℛy]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (algebraMap R A (counit y) * antipode R (ℛx.right i)) := by
        simp only [Algebra.smul_def, mul_one]
      _ = ∑ i ∈ ℛx.index, algebraMap R A (counit y) * (ℛx.left i * antipode R (ℛx.right i)) := by
        congr 1; ext i; rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
      _ = algebraMap R A (counit y) * ∑ i ∈ ℛx.index, ℛx.left i * antipode R (ℛx.right i) := by
        rw [← Finset.mul_sum]
      _ = algebraMap R A (counit y) * (counit (R := R) x • (1 : A)) := by
        rw [sum_mul_antipode_eq_smul ℛx]
      _ = (counit (R := R) x * counit y) • (1 : A) := by
        simp only [Algebra.smul_def, mul_one, ← map_mul, mul_comm (counit x)]
      _ = (counit (R := R) y • counit x) • (1 : A) := by
        simp only [smul_eq_mul, mul_comm (counit y)]

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
