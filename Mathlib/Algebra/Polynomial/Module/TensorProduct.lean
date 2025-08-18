/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George McNinch
-/

import Mathlib

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
def TensorProductEquivPolynomialModule : (R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M) :=
  let incl : ℕ → M →ₗ[R] R[X] ⊗[R] M := fun n =>
    TensorProduct.mk R R[X] M (monomial n 1)
  { toFun := (PolynomialModule.TensorProduct.mk R M).toFun

    map_add' := (PolynomialModule.TensorProduct.mk R M).map_add

    map_smul' := (PolynomialModule.TensorProduct.mk R M).map_smul

    invFun := Finsupp.lsum R incl

    left_inv := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul h y  =>
          simp only [PolynomialModule.TensorProduct.mk, PolynomialModule.Pairing,
                     PolynomialModule.MulByPolynomial,
                     AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
                     AddHom.coe_mk, lift.tmul, LinearMap.coe_mk
                     ]
          rw [ LinearMap.comp_apply ]
          induction h using Polynomial.induction_on' with
          | add p q hp hq =>
              rw [ add_tmul ]
              simp_all only [DistribMulAction.toModuleEnd_apply,
                LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply, incl ]
              rw [add_smul]
              rw [←hp, ←hq]
              simp only [map_add]
          | monomial j t =>
              simp only [DistribMulAction.toModuleEnd_apply,
                LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply]
              rw [Finsupp.lsum_apply R incl]
              have : ((monomial j) t • (PolynomialModule.lsingle R 0) y)
                  = (PolynomialModule.lsingle R j) (t • y) := by
                refine PolynomialModule.monomial_smul_single (M := M) j t 0 y
              rw [this]

              have pm_sum_lsingle_index {z : M}
                  {g : ℕ → M → R[X] ⊗[R] M} (hg : g j 0 = 0) :
                  Finsupp.sum ((PolynomialModule.lsingle R j) z) g = g j z := by
                apply Finsupp.sum_single_index ?_
                · exact hg
              rw [pm_sum_lsingle_index (z := t•y) (by simp only [map_zero])]
              unfold incl
              simp only [map_smul, TensorProduct.mk_apply]
              rw [TensorProduct.smul_tmul', Polynomial.smul_monomial]
              simp only [smul_eq_mul, mul_one]

      | add w₁ w₂ hw₁ hw₂ =>
          rw [ (PolynomialModule.TensorProduct.mk R M).map_add' w₁ w₂ ]
          rw [ map_add ]
          rw [ hw₁, hw₂ ]

    right_inv := by
      intro v
      induction v using PolynomialModule.induction_linear with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ =>
          rw [ map_add ]
          rw [ (PolynomialModule.TensorProduct.mk R M).map_add' ]
          rw [ hw₁, hw₂ ]
      | single j x =>
          simp only [PolynomialModule.TensorProduct.mk, PolynomialModule.Pairing]
          rw [Finsupp.lsum_apply R incl]
          have pm_sum_single_index {z : M}
              {g : ℕ → M → R[X] ⊗[R] M} (hg : g j 0 = 0) :
              Finsupp.sum ((PolynomialModule.single R j) z) g = g j z :=  by
            apply Finsupp.sum_single_index ?_
            · exact hg
          rw [pm_sum_single_index (by simp)]
          simp_all only [PolynomialModule.MulByPolynomial, DistribMulAction.toModuleEnd_apply,
            mk_apply, AddHom.toFun_eq_coe, lift.tmul',
            LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
            Function.comp_apply, DistribMulAction.toLinearMap_apply, incl]
          have monomial_smul_lsingle (j : ℕ) (r : R) (k : ℕ) (m : M) :
              (Polynomial.monomial j) r • (PolynomialModule.lsingle R k) m =
              (PolynomialModule.lsingle R (j + k)) (r • m) := by
            apply PolynomialModule.monomial_smul_single
          rw [monomial_smul_lsingle j 1 0 x]
          simp only [add_zero, one_smul]
          rfl
   }

end
