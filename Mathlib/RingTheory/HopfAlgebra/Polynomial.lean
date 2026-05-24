/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Hopf algebra structure on polynomials (additive group scheme 𝔾ₐ)

The polynomial ring `R[X]` carries a natural Hopf algebra structure encoding the
additive group scheme `𝔾ₐ`:
* comultiplication: `Δ(X) = X ⊗ 1 + 1 ⊗ X` (encoding `p(x) ↦ p(x + x')`)
* counit: `ε(p) = p(0)` (evaluation at zero)
* antipode: `S(X) = -X` (requires `CommRing R`)

This is dual to the multiplicative group scheme `𝔾ₘ` formalized via Laurent polynomials
in `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`.

## Main definitions

* `Polynomial.instCoalgebraStruct`: the `R`-coalgebra structure data on `R[X]`.
* `Polynomial.instCoalgebra`: the `R`-coalgebra instance on `R[X]` with additive
  comultiplication.
* `Polynomial.instBialgebra`: the `R`-bialgebra structure on `R[X]`.
* `Polynomial.instHopfAlgebra`: the `R`-Hopf algebra structure on `R[X]` when `R` is a
  commutative ring.

## Implementation notes

The coalgebra axioms are equalities of linear maps, but both sides factor through
algebra homomorphisms out of `R[X]`. Since `R[X]` is free on `X`, algebra hom equality
reduces to checking on `X` alone (`Polynomial.algHom_ext`). The proofs convert between the
linear map API (`rTensor`, `lTensor`, `TensorProduct.assoc`) and the algebra hom API
(`Algebra.TensorProduct.map`, `includeRight`, `Algebra.TensorProduct.assoc`) via
auxiliary lemmas, then apply `algHom_ext`.

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2
-/

public section

noncomputable section

open Polynomial TensorProduct

open scoped Polynomial TensorProduct

namespace Polynomial

variable (R : Type*) [CommSemiring R]

/-! ### Coalgebra structure and instance

The three coalgebra axioms (coassociativity, left counitality, right counitality)
reduce to checking equality of `R`-algebra hom compositions on the generator `X`.
-/

/-- The `𝔾ₐ` coalgebra structure on `R[X]`: comultiplication sends `X` to `X ⊗ 1 + 1 ⊗ X`
and counit evaluates at zero. -/
instance instCoalgebraStruct : CoalgebraStruct R R[X] where
  comul := (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))).toLinearMap
  counit := (Polynomial.aeval (0 : R)).toLinearMap

theorem comul_def :
    (Coalgebra.comul : R[X] →ₗ[R] R[X] ⊗[R] R[X]) =
    (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))).toLinearMap := rfl

theorem counit_def :
    (Coalgebra.counit : R[X] →ₗ[R] R) =
    (Polynomial.aeval (0 : R)).toLinearMap := rfl

theorem comul_apply (p : R[X]) :
    Coalgebra.comul (R := R) p =
    Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X])) p := rfl

theorem counit_apply (p : R[X]) :
    Coalgebra.counit (R := R) p = Polynomial.aeval (0 : R) p := rfl

@[simp]
theorem comul_X :
    Coalgebra.comul (R := R) (X : R[X]) = (X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]) := by
  simp [comul_apply]

@[simp]
theorem comul_C (r : R) :
    Coalgebra.comul (R := R) (C r : R[X]) = (C r) ⊗ₜ 1 := by
  simp [comul_apply]

@[simp]
theorem counit_X :
    Coalgebra.counit (R := R) (X : R[X]) = 0 := by
  simp [counit_apply]

@[simp]
theorem counit_C (r : R) :
    Coalgebra.counit (R := R) (C r : R[X]) = r := by
  simp [counit_apply]

-- Glue lemmas connecting rTensor/lTensor of AlgHom.toLinearMap to Algebra.TensorProduct.map
private theorem rTensor_toLinearMap_eq (f : R[X] →ₐ[R] A) :
    f.toLinearMap.rTensor R[X] =
    (Algebra.TensorProduct.map f (AlgHom.id R R[X])).toLinearMap := by
  ext x y; simp [LinearMap.rTensor_tmul]

private theorem lTensor_toLinearMap_eq (f : R[X] →ₐ[R] A) :
    f.toLinearMap.lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X]) f).toLinearMap := by
  ext x y; simp [LinearMap.lTensor_tmul]

/-- The `𝔾ₐ` coalgebra instance on `R[X]`: coassociativity holds because both
`(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ` send `X` to `X⊗1⊗1 + 1⊗X⊗1 + 1⊗1⊗X`. -/
instance instCoalgebra : Coalgebra R R[X] where
  rTensor_counit_comp_comul := by
    rw [counit_def, comul_def, rTensor_toLinearMap_eq,
        Algebra.TensorProduct.toLinearMap_includeRight]
    congr 1
    apply Polynomial.algHom_ext
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply]
  lTensor_counit_comp_comul := by
    rw [counit_def, comul_def, lTensor_toLinearMap_eq,
        Algebra.TensorProduct.toLinearMap_includeLeft]
    congr 1
    apply Polynomial.algHom_ext
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
  coassoc := by
    rw [comul_def, rTensor_toLinearMap_eq, lTensor_toLinearMap_eq]
    congr 1
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
          AlgHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, aeval_X,
          map_add, map_one, Algebra.TensorProduct.one_def,
          Algebra.TensorProduct.assoc_tmul,
          TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel

/-! ### Bialgebra instance -/

/-- The `𝔾ₐ` bialgebra instance on `R[X]`: the comultiplication and counit are algebra
homomorphisms by construction. -/
instance instBialgebra : Bialgebra R R[X] :=
  Bialgebra.mk' R R[X]
    (by simp [counit_apply])
    (fun {a b} => by simp [counit_apply, map_mul])
    (by simp [comul_apply])
    (fun {a b} => by simp [comul_apply, map_mul])

end Polynomial

end -- end CommSemiring section

/-! ### Hopf algebra instance -/

noncomputable section

open Polynomial TensorProduct

open scoped Polynomial TensorProduct

namespace Polynomial

variable (R : Type*) [CommRing R]

/-- The antipode on `R[X]` for the additive group scheme `𝔾ₐ`:
the unique `R`-algebra homomorphism sending `X ↦ -X`.
This is "inversion" on `𝔾ₐ`: if `Δ` encodes addition (`x ↦ x + x'`),
then `S` encodes negation (`x ↦ -x`). -/
def antipodeAdditiveAlgHom : R[X] →ₐ[R] R[X] :=
  Polynomial.aeval (-X : R[X])

@[simp]
theorem antipodeAdditiveAlgHom_X :
    antipodeAdditiveAlgHom R (X : R[X]) = -X := by
  simp [antipodeAdditiveAlgHom]

@[simp]
theorem antipodeAdditiveAlgHom_C (r : R) :
    antipodeAdditiveAlgHom R (C r) = C r := by
  simp [antipodeAdditiveAlgHom]

/-- The `𝔾ₐ` Hopf algebra instance on `R[X]` (requires `CommRing R` for the antipode
`S(X) = -X`). The antipode axiom `m ∘ (S ⊗ id) ∘ Δ = η ∘ ε` holds because both sides
send `X` to `0`: `S(X) · 1 + 1 · X = -X + X = 0 = C(ε(X))`. -/
instance instHopfAlgebra : HopfAlgebra R R[X] where
  antipode := (antipodeAdditiveAlgHom R).toLinearMap
  mul_antipode_rTensor_comul := by
    have rTensor_eq : (antipodeAdditiveAlgHom R).toLinearMap.rTensor R[X] =
        (Algebra.TensorProduct.map (antipodeAdditiveAlgHom R)
         (AlgHom.id R R[X])).toLinearMap := by
      ext x y; simp [LinearMap.rTensor_tmul]
    rw [comul_def, counit_def, rTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap]
    congr 1; apply Polynomial.algHom_ext
    simp [antipodeAdditiveAlgHom,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.ofId_apply]
  mul_antipode_lTensor_comul := by
    have lTensor_eq : (antipodeAdditiveAlgHom R).toLinearMap.lTensor R[X] =
        (Algebra.TensorProduct.map (AlgHom.id R R[X])
         (antipodeAdditiveAlgHom R)).toLinearMap := by
      ext x y; simp [LinearMap.lTensor_tmul]
    rw [comul_def, counit_def, lTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap]
    congr 1; apply Polynomial.algHom_ext
    simp [antipodeAdditiveAlgHom,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.ofId_apply]

end Polynomial

end
