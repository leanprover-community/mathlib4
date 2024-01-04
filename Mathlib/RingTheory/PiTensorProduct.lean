/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Group.Pi

/-!
# Tensor product of `R`-algebras and rings

If `(Aᵢ)` is a family of `R`-algebras then the `R`-tensor `⨂ᵢ Aᵢ` is an `R`-algebra as well with
its structure map defined by `r ↦ r • 1`.

In particular if we take `R` to be `ℤ`, then this collapse into tensor product of rings.
-/

open TensorProduct Function

variable {ι R : Type*} {A : ι → Type*}

namespace PiTensorProduct

noncomputable section AddCommMonoidWithOne

variable [CommSemiring R] [∀ i, AddCommMonoidWithOne (A i)] [∀ i, Module R (A i)]

instance one : One (⨂[R] i, A i) where
  one := tprod R 1

instance addCommMonoidWithOne : AddCommMonoidWithOne (⨂[R] i, A i) where
  __ := inferInstanceAs (AddCommMonoid (⨂[R] i, A i))
  __ := one

end AddCommMonoidWithOne

noncomputable section Semiring

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/--
The multiplication in tensor product of rings is induced by `(xᵢ) * (yᵢ) = (xᵢ * yᵢ)`
-/
def lmul : (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) :=
lift
{ toFun := fun x ↦ lift
    { toFun := fun y ↦ tprod _ (x * y)
      map_add' := fun z i a a' ↦ by
        dsimp
        rw [show x * update z i (a + a') = update (x * z) i (x i * (a + a')) by
        · ext j
          simp only [Pi.mul_apply, update]
          aesop]
        rw [mul_add, MultilinearMap.map_add]
        congr <;> ext j <;> simp only [update, Pi.mul_apply] <;> aesop
      map_smul' := fun z i r a ↦ by
        dsimp
        rw [show x * update z i (r • a) = update (x * z) i (x i * (r • a)) by
        · ext j
          simp only [Pi.mul_apply, update, Algebra.mul_smul_comm]
          split_ifs <;> aesop,
        show x i * r • a = r • (x i * a) by simp only [Algebra.mul_smul_comm]]
        rw [MultilinearMap.map_smul]
        congr
        ext j
        simp only [update, Pi.mul_apply]
        aesop }
  map_add' := fun z i a a' ↦ by
    ext z'
    simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.coe_mk,
      LinearMap.add_apply]
    rw [show update z i (a + a') * z' = update (z * z') i ((a + a') * (z' i)) by
    · ext j
      simp only [Pi.mul_apply, update]
      aesop]
    rw [add_mul, MultilinearMap.map_add]
    congr <;> ext j <;> simp only [update, Pi.mul_apply] <;> aesop
  map_smul' := fun z i r a ↦ by
    ext z'
    simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.coe_mk,
      LinearMap.smul_apply]
    rw [show update z i (r • a) * z' = update (z * z') i ((r • a) * z' i) by
    · ext j
      simp only [Pi.mul_apply, update]
      aesop]
    rw [Algebra.smul_mul_assoc, MultilinearMap.map_smul]
    congr
    ext j
    simp only [update, Pi.mul_apply]
    aesop }

@[simp] lemma lmul_tprod_tprod (x y : (i : ι) → A i) :
    lmul (tprod R x) (tprod R y) = tprod R (x * y) := by
  simp only [lmul, lift.tprod, MultilinearMap.coe_mk]

lemma lmul_assoc (x y z : ⨂[R] i, A i) : lmul (lmul x y) z = lmul x (lmul y z) := by
  induction' x using PiTensorProduct.induction_on with rx x x₁ x₂ hx₁ hx₂
  · induction' y using PiTensorProduct.induction_on with ry y y₁ y₂ hy₁ hy₂
    · induction' z using PiTensorProduct.induction_on with rz z z₁ z₂ hz₁ hz₂
      · simp only [map_smul, LinearMap.smul_apply, lmul_tprod_tprod, mul_assoc]
      · simp only [map_smul, LinearMap.smul_apply, lmul_tprod_tprod, map_add] at hz₁ hz₂ ⊢
        rw [hz₁, hz₂]
    · simp only [map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply] at hy₁ hy₂ ⊢
      rw [hy₁, hy₂]
  · simp only [map_add, LinearMap.add_apply] at hx₁ hx₂ ⊢
    rw [hx₁, hx₂]

lemma one_lmul (x : ⨂[R] i, A i) : lmul (tprod R 1) x = x := by
  induction' x using PiTensorProduct.induction_on with rx x x₁ x₂ hx₁ hx₂
  · simp
  · simp only [map_add, hx₁, hx₂]

lemma lmul_one (x : ⨂[R] i, A i) : lmul x (tprod R 1) = x := by
  induction' x using PiTensorProduct.induction_on with rx x x₁ x₂ hx₁ hx₂
  · simp
  · simp only [map_add, LinearMap.add_apply, hx₁, hx₂]

lemma zero_lmul (x : ⨂[R] i, A i) : lmul 0 x = 0 := by
  induction' x using PiTensorProduct.induction_on <;> simp

lemma lmul_zero (x : ⨂[R] i, A i) : lmul x 0 = 0 := by
  induction' x using PiTensorProduct.induction_on <;> simp

lemma lmul_add (x y z : ⨂[R] i, A i) : lmul x (y + z) = lmul x y + lmul x z := by
  induction' x using PiTensorProduct.induction_on <;> simp

lemma add_lmul (x y z : ⨂[R] i, A i) : lmul (x + y) z = lmul x z + lmul y z := by
  induction' x using PiTensorProduct.induction_on <;> simp

instance mul : Mul (⨂[R] i, A i) where
  mul x y := lmul x y

lemma mul_def (x y : ⨂[R] i, A i) : x * y = lmul x y := rfl

@[simp] lemma tprod_mul_tprod (x y : (i : ι) → A i) :
    (tprod R x) * (tprod R y) = tprod R (x * y) :=
  lmul_tprod_tprod x y

lemma smul_tprod_mul_smul_tprod (r s : R) (x y : Π i, A i) :
    (r • tprod R x) * (s • tprod R y) = (r * s) • (tprod R (x * y)) := by
  change lmul _ _ = _
  rw [map_smul, map_smul, mul_comm r s, mul_smul]
  simp only [LinearMap.smul_apply, lmul_tprod_tprod]

instance monoid : Monoid (⨂[R] i, A i) where
  __ := mul
  __ := one
  mul_assoc := lmul_assoc
  one_mul := one_lmul
  mul_one := lmul_one

instance semiring : Semiring (⨂[R] i, A i) where
  __ := monoid
  __ := inferInstanceAs <| AddCommMonoidWithOne (⨂[R] i, A i)
  left_distrib := lmul_add
  right_distrib := add_lmul
  zero_mul := zero_lmul
  mul_zero := lmul_zero

instance algebra : Algebra R (⨂[R] i, A i) where
  __ := hasSMul'
  toFun := (· • 1)
  map_one' := by simp
  map_mul' r s :=show (r * s) • 1 = lmul (r • 1) (s • 1)  by
    rw [map_smul, map_smul, LinearMap.smul_apply, mul_comm, mul_smul]
    congr
    show (1 : ⨂[R] i, A i) = 1 * 1
    rw [mul_one]
  map_zero' := by simp
  map_add' := by simp [add_smul]
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change lmul _ _ = lmul _ _
    rw [map_smul, map_smul, LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one, one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = lmul _ _
    rw [map_smul, LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]

/--
the map `Aᵢ ⟶ ⨂ᵢ Aᵢ` given by `a ↦ 1 ⊗ ... ⊗ a ⊗ 1 ⊗ ...`
-/
@[simps]
def fromComponentAlgHom [DecidableEq ι] (i : ι) : A i →ₐ[R] ⨂[R] i, A i where
  toFun a := tprod R (MonoidHom.single _ i a)
  map_one' := by simp only [_root_.map_one]; rfl
  map_mul' a a' := by simp
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one]
    erw [smul_tprodCoeff]
    rfl

/--
Lifting a multilinear map to an algebra homomorphism from tensor product
-/
@[simps]
def liftAlgHom {S : Type*} [Semiring S] [Algebra R S]
    (f : MultilinearMap R A S)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : (⨂[R] i, A i) →ₐ[R] S where
  toFun := lift f
  map_one' := show lift f (tprod R 1) = 1 by simp [one]
  map_mul' x y := show lift f (x * y) = lift f x * lift f y by
    induction' x using PiTensorProduct.induction_on with rx x x₁ x₂ hx₁ hx₂
    · induction' y using PiTensorProduct.induction_on with ry y y₁ y₂ hy₁ hy₂
      · simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, tprod_mul_tprod, map_smul,
          lift.tprod, mul]
      · simp only [Algebra.smul_mul_assoc, map_smul, lift.tprod, map_add] at hy₁ hy₂ ⊢
        rw [mul_add, map_add, smul_add, hy₁, hy₂, mul_add, smul_add]
    · simp only [map_add] at hx₁ hx₂ ⊢
      rw [add_mul, map_add, hx₁, hx₂, add_mul]
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]
  commutes' r := show lift f (r • tprod R 1) = _ by
    rw [map_smul, lift.tprod, one, Algebra.algebraMap_eq_smul_one]

end Semiring

noncomputable section Ring

variable [CommRing R] [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]

instance ring : Ring (⨂[R] i, A i) where
  __ := semiring
  __ := inferInstanceAs <| AddCommGroup (⨂[R] i, A i)

end Ring

noncomputable section CommSemiring

variable [CommSemiring R] [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]

lemma lmul_comm (x y : ⨂[R] i, A i) : lmul x y = lmul y x :=  by
  induction' x using PiTensorProduct.induction_on with rx x x₁ x₂ hx₁ hx₂
  · induction' y using PiTensorProduct.induction_on with ry y y₁ y₂ hy₁ hy₂
    · simp only [map_smul, LinearMap.smul_apply, lmul_tprod_tprod]
      rw [smul_comm, mul_comm]
    · simp only [map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply,
        smul_add] at hy₁ hy₂ ⊢
      rw [hy₁, hy₂]
  · simp only [map_add, LinearMap.add_apply] at hx₁ hx₂ ⊢
    rw [hx₁, hx₂]

instance commSemiring : CommSemiring (⨂[R] i, A i) where
  __ := semiring
  __ := inferInstanceAs <| AddCommMonoid (⨂[R] i, A i)
  mul_comm := lmul_comm

end CommSemiring

noncomputable section CommRing

variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
instance commRing : CommRing (⨂[R] i, A i) where
  __ := commSemiring
  __ := inferInstanceAs <| AddCommGroup (⨂[R] i, A i)

end CommRing

end PiTensorProduct
