/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George McNinch
-/

import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# `PolynomialModule` and the tensor product

For a commutative ring `R` and an `R`-module `M`, there is an
equivalence between the `R[X]`-modules `R[X] ⊗[R] M` and
`PolynomialModule R M`; see `TensorProductEquivPolynomialModule`.

To obtain the equivalence, we first construct the bilinear mapping
`R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`; see `MulByPolynomial` and
`Pairing`.

The universal property of the tensor product (`TensorProduct.lift`)
then converts `Pairing` into the required `toFun` for the
equivalence. See `TensorMap` for the construction of the mapping

```
R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M
```

including confirmation that this mapping is `R[X]`-linear.

Finally, the `invFun`

```
PolynomialModule R M →ₗ[R] R[X] ⊗[R] M

```

is constructed in `TensorProductEquivPolynomialModule` from the
inclusions mappings

```
fun (n : ℕ) => TensorProduct.mk R R[X] M (monomial n 1) : ℕ → M →ₗ[R] R[X] ⊗[R] M

```
using `Finsupp.lsum R`.
-/

open Polynomial
open TensorProduct
open LinearMap

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace PolynomialModule

/--
For a polynomial `f:R[X]`, and an R-module M, multiplication
by f determines an R-module homomorphism `M →ₗ[R] PolynomialModule R M`
-/
def MulByPolynomial (f : R[X]) : M →ₗ[R] PolynomialModule R M :=
  (DistribMulAction.toModuleEnd R[X] (PolynomialModule R M) f) ∘ₗ
    (PolynomialModule.lsingle R 0)

/-- The bilinear mapping `R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`
given by the rule `f ↦ m ↦ (MulByPolynomial f) m`
-/
def Pairing (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M where
  toFun :=  MulByPolynomial
  map_add' f g := by
    ext
    rw [ MulByPolynomial, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply ]
    exact  add_smul f g _
  map_smul' t f := by
    rw [ RingHom.id_apply ]
    ext
    unfold MulByPolynomial
    simp

/--
The `R[X]`-linear mapping `R[X] ⊗[R] M → PolynomialModule R M`
build from the bilinear mapping `BilinToPolyMod` `TensorProduct.lift`.

The mapping property of the tensor product gives the underyling
`R`-linear mapping, which is then confirmed to be `R[X]`-linear using
`TensorProduct.induction_on`
-/
def TensorProduct.mk (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M :=
  let φ : R[X] ⊗[R] M →ₗ[R] PolynomialModule R M := lift (Pairing R M)
  { toFun := φ.toFun

    map_add' := φ.map_add

    map_smul' := by
      intro g x
      rw [ RingHom.id_apply
         , AddHom.toFun_eq_coe
         , LinearMap.coe_toAddHom ]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul h y =>
          unfold φ
          rw [ smul_tmul', lift.tmul, lift.tmul , smul_eq_mul ]
          simp only [Pairing, MulByPolynomial, LinearMap.coe_mk,
            AddHom.coe_mk ]
          rw [ LinearMap.comp_apply, LinearMap.comp_apply ]
          simp only [DistribMulAction.toModuleEnd_apply,
            LinearMap.coe_restrictScalars, DistribMulAction.toLinearMap_apply]
          rw [ ←smul_eq_mul, smul_assoc ]
      | add x y hx hy =>
          rw [ smul_add, map_add, map_add, smul_add ]
          rw [ hx ,hy ]
    }

end PolynomialModule



/-- The `R[X]` linear equivalence `(R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M)`.
-/
def polynomialTensorProductLEquivPolynomialModule : R[X] ⊗[R] M ≃ₗ[R[X]] PolynomialModule R M :=
  let e := liftBaseChange R[X] <| PolynomialModule.lsingle R (M := M) 0
  let inv : PolynomialModule R M →ₗ[R] _ :=
    Finsupp.lsum R fun n ↦ TensorProduct.mk R R[X] M (X ^ n)
  have left : inv ∘ₗ e = .id := by
    ext n x
    simpa [inv, e] using (Finsupp.sum_single_index (by simp)).trans <| by
      simp [monomial_one_right_eq_X_pow]
  have right : e.restrictScalars R ∘ₗ inv = .id := by
    refine Finsupp.lhom_ext' fun n ↦ LinearMap.ext fun x ↦ ?_
    simpa [e, inv, ← monomial_one_right_eq_X_pow] using by rfl
  { __ := e
    invFun := inv
    left_inv := (congr($left ·))
    right_inv := (congr($right ·)) }
