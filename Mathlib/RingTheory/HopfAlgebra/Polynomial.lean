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

* `Polynomial.instCoalgebra`: the `R`-coalgebra structure on `R[X]` with additive
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

noncomputable section

open Polynomial TensorProduct

open scoped Polynomial TensorProduct

namespace Polynomial

variable (R : Type*) [CommSemiring R]

/-! ### Comultiplication and counit -/

/-- The comultiplication on `R[X]` for the additive group scheme `𝔾ₐ`:
the unique `R`-algebra homomorphism sending `X ↦ X ⊗ 1 + 1 ⊗ X`.
As a linear map, this encodes `Δ(p(x)) = p(x + x')`. -/
def comulAdditiveAlgHom : R[X] →ₐ[R] R[X] ⊗[R] R[X] :=
  Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))

/-- The counit on `R[X]` for the additive group scheme `𝔾ₐ`:
evaluation at `0`, as an `R`-algebra homomorphism. This is `ε(p) = p(0)`. -/
def counitAdditiveAlgHom : R[X] →ₐ[R] R :=
  Polynomial.aeval (0 : R)

@[simp]
theorem comulAdditiveAlgHom_X :
    comulAdditiveAlgHom R (X : R[X]) = (X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]) := by
  simp [comulAdditiveAlgHom]

@[simp]
theorem comulAdditiveAlgHom_C (r : R) :
    comulAdditiveAlgHom R (C r) = (C r) ⊗ₜ 1 := by
  simp [comulAdditiveAlgHom]

@[simp]
theorem counitAdditiveAlgHom_X :
    counitAdditiveAlgHom R (X : R[X]) = 0 := by
  simp [counitAdditiveAlgHom]

@[simp]
theorem counitAdditiveAlgHom_C (r : R) :
    counitAdditiveAlgHom R (C r) = r := by
  simp [counitAdditiveAlgHom]

/-! ### Coalgebra instance

The three coalgebra axioms (coassociativity, left counitality, right counitality)
reduce to checking equality of `R`-algebra hom compositions on the generator `X`.
-/

/-- The `𝔾ₐ` coalgebra structure on `R[X]`. -/
instance instCoalgebraStruct : CoalgebraStruct R R[X] where
  comul := (comulAdditiveAlgHom R).toLinearMap
  counit := (counitAdditiveAlgHom R).toLinearMap

-- Auxiliary equations for unfolding the CoalgebraStruct fields
theorem comul_eq : (CoalgebraStruct.comul : R[X] →ₗ[R] _) =
    (comulAdditiveAlgHom R).toLinearMap := rfl

theorem counit_eq : (CoalgebraStruct.counit : R[X] →ₗ[R] _) =
    (counitAdditiveAlgHom R).toLinearMap := rfl

-- Glue lemmas connecting rTensor/lTensor to Algebra.TensorProduct.map
theorem rTensor_counit_eq :
    (counitAdditiveAlgHom R).toLinearMap.rTensor R[X] =
    (Algebra.TensorProduct.map (counitAdditiveAlgHom R)
     (AlgHom.id R R[X])).toLinearMap := by
  ext x y; simp [LinearMap.rTensor_tmul]

theorem lTensor_counit_eq :
    (counitAdditiveAlgHom R).toLinearMap.lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X])
     (counitAdditiveAlgHom R)).toLinearMap := by
  ext x y; simp [LinearMap.lTensor_tmul]

theorem mk_one_eq_includeRight :
    TensorProduct.mk R R R[X] 1 =
    (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] R ⊗[R] R[X]).toLinearMap := by
  ext y; simp [Algebra.TensorProduct.includeRight_apply]

theorem mk_flip_one_eq_includeLeft :
    (TensorProduct.mk R R[X] R).flip 1 =
    (Algebra.TensorProduct.includeLeft : R[X] →ₐ[R] R[X] ⊗[R] R).toLinearMap := by
  ext y; simp [Algebra.TensorProduct.includeLeft_apply, LinearMap.flip_apply]

theorem rTensor_comul_eq :
    (comulAdditiveAlgHom R).toLinearMap.rTensor R[X] =
    (Algebra.TensorProduct.map (comulAdditiveAlgHom R)
     (AlgHom.id R R[X])).toLinearMap := by
  ext x y; simp [LinearMap.rTensor_tmul]

theorem lTensor_comul_eq :
    (comulAdditiveAlgHom R).toLinearMap.lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X])
     (comulAdditiveAlgHom R)).toLinearMap := by
  ext x y; simp [LinearMap.lTensor_tmul]

/-- The `𝔾ₐ` coalgebra instance on `R[X]`: coassociativity holds because both
`(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ` send `X` to `X⊗1⊗1 + 1⊗X⊗1 + 1⊗1⊗X`. -/
instance instCoalgebra : Coalgebra R R[X] :=
  { instCoalgebraStruct R with
    rTensor_counit_comp_comul := by
      rw [counit_eq, comul_eq, rTensor_counit_eq, mk_one_eq_includeRight]
      change ((Algebra.TensorProduct.map (counitAdditiveAlgHom R)
               (AlgHom.id R R[X])).comp (comulAdditiveAlgHom R)).toLinearMap = _
      congr 1
      apply Polynomial.algHom_ext
      simp [comulAdditiveAlgHom, counitAdditiveAlgHom,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply]
    lTensor_counit_comp_comul := by
      rw [counit_eq, comul_eq, lTensor_counit_eq, mk_flip_one_eq_includeLeft]
      change ((Algebra.TensorProduct.map (AlgHom.id R R[X])
               (counitAdditiveAlgHom R)).comp (comulAdditiveAlgHom R)).toLinearMap = _
      congr 1
      apply Polynomial.algHom_ext
      simp [comulAdditiveAlgHom, counitAdditiveAlgHom,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
    coassoc := by
      rw [comul_eq, rTensor_comul_eq, lTensor_comul_eq]
      change ((Algebra.TensorProduct.assoc R R R R[X] R[X] R[X]).toAlgHom.comp
              ((Algebra.TensorProduct.map (comulAdditiveAlgHom R)
                (AlgHom.id R R[X])).comp
               (comulAdditiveAlgHom R))).toLinearMap =
             ((Algebra.TensorProduct.map (AlgHom.id R R[X])
               (comulAdditiveAlgHom R)).comp
              (comulAdditiveAlgHom R)).toLinearMap
      congr 1
      apply Polynomial.algHom_ext
      simp only [comulAdditiveAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
            AlgHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, aeval_X,
            map_add, map_one, Algebra.TensorProduct.one_def,
            Algebra.TensorProduct.assoc_tmul,
            TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel }

/-! ### Bialgebra instance -/

/-- The `𝔾ₐ` bialgebra instance on `R[X]`: the comultiplication and counit are algebra
homomorphisms by construction. -/
instance instBialgebra : Bialgebra R R[X] :=
  Bialgebra.mk' R R[X]
    (by simp [counit_eq])
    (by intro a b; simp [counit_eq, map_mul])
    (by simp [comul_eq])
    (by intro a b; simp [comul_eq, map_mul])

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
    rw [comul_eq, counit_eq, rTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap]
    -- Both sides are toLinearMap of algebra hom compositions. Convert and check on X.
    change ((Algebra.TensorProduct.lmul' R : R[X] ⊗[R] R[X] →ₐ[R] R[X]).comp
            ((Algebra.TensorProduct.map (antipodeAdditiveAlgHom R)
              (AlgHom.id R R[X])).comp (comulAdditiveAlgHom R))).toLinearMap =
           ((Algebra.ofId R R[X]).comp (counitAdditiveAlgHom R)).toLinearMap
    congr 1; apply Polynomial.algHom_ext
    simp [comulAdditiveAlgHom, antipodeAdditiveAlgHom, counitAdditiveAlgHom,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.ofId_apply]
  mul_antipode_lTensor_comul := by
    have lTensor_eq : (antipodeAdditiveAlgHom R).toLinearMap.lTensor R[X] =
        (Algebra.TensorProduct.map (AlgHom.id R R[X])
         (antipodeAdditiveAlgHom R)).toLinearMap := by
      ext x y; simp [LinearMap.lTensor_tmul]
    rw [comul_eq, counit_eq, lTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap]
    change ((Algebra.TensorProduct.lmul' R : R[X] ⊗[R] R[X] →ₐ[R] R[X]).comp
            ((Algebra.TensorProduct.map (AlgHom.id R R[X])
              (antipodeAdditiveAlgHom R)).comp (comulAdditiveAlgHom R))).toLinearMap =
           ((Algebra.ofId R R[X]).comp (counitAdditiveAlgHom R)).toLinearMap
    congr 1; apply Polynomial.algHom_ext
    simp [comulAdditiveAlgHom, antipodeAdditiveAlgHom, counitAdditiveAlgHom,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.ofId_apply]

end Polynomial

end
