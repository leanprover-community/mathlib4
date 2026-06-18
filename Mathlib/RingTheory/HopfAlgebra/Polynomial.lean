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

The coalgebra axioms are equalities of linear maps out of `R[X]`. Since comultiplication
and counit are defined via `Polynomial.aeval`, each axiom reduces to checking on the
generator `X`, exploiting the universal property of the polynomial ring.

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2
-/

public section

noncomputable section

open Polynomial TensorProduct

open scoped Polynomial TensorProduct

namespace Polynomial

variable (R : Type*) [CommSemiring R]

/-! ### Coalgebra structure and instance -/

/-- The `𝔾ₐ` coalgebra structure on `R[X]`. -/
instance instCoalgebraStruct : CoalgebraStruct R R[X] where
  comul := (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))).toLinearMap
  counit := (Polynomial.aeval (0 : R)).toLinearMap

theorem comul_def :
    (Coalgebra.comul : R[X] →ₗ[R] R[X] ⊗[R] R[X]) =
    (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))).toLinearMap := rfl

theorem counit_def :
    (Coalgebra.counit : R[X] →ₗ[R] R) = (Polynomial.aeval (0 : R)).toLinearMap := rfl

@[simp]
theorem comul_apply (p : R[X]) :
    Coalgebra.comul (R := R) p =
    Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X])) p := rfl

@[simp]
theorem counit_apply (p : R[X]) :
    Coalgebra.counit (R := R) p = Polynomial.aeval (0 : R) p := rfl

-- Glue lemmas connecting rTensor/lTensor of AlgHom.toLinearMap to Algebra.TensorProduct.map
private theorem rTensor_toLinearMap_eq {A : Type*} [CommSemiring A] [Algebra R A]
    (f : R[X] →ₐ[R] A) :
    f.toLinearMap.rTensor R[X] =
    (Algebra.TensorProduct.map f (AlgHom.id R R[X])).toLinearMap := by
  ext x y; simp [LinearMap.rTensor_tmul]

private theorem lTensor_toLinearMap_eq {A : Type*} [CommSemiring A] [Algebra R A]
    (f : R[X] →ₐ[R] A) :
    f.toLinearMap.lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X]) f).toLinearMap := by
  ext x y; simp [LinearMap.lTensor_tmul]

/-- The `𝔾ₐ` coalgebra instance on `R[X]`. -/
instance instCoalgebra : Coalgebra R R[X] where
  rTensor_counit_comp_comul := by
    rw [counit_def, comul_def, rTensor_toLinearMap_eq, ← AlgHom.comp_toLinearMap,
        ← AlgebraTensorModule.mk_eq, ← Algebra.TensorProduct.toLinearMap_includeRight]
    congr 1; apply Polynomial.algHom_ext
    simp
  lTensor_counit_comp_comul := by
    rw [counit_def, comul_def, lTensor_toLinearMap_eq, ← AlgHom.comp_toLinearMap,
        ← AlgebraTensorModule.mk_eq, ← Algebra.TensorProduct.toLinearMap_includeLeft]
    congr 1; apply Polynomial.algHom_ext
    simp
  coassoc := by
    rw [comul_def, rTensor_toLinearMap_eq, lTensor_toLinearMap_eq]
    apply LinearMap.ext; intro p
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
    | monomial n r =>
      have hassoc : ∀ x, (TensorProduct.assoc R R[X] R[X] R[X]) x =
          (Algebra.TensorProduct.assoc R R R[X] R[X] R[X] R[X]) x := fun _ => rfl
      simp [← C_mul_X_pow_eq_monomial, hassoc, Algebra.TensorProduct.one_def,
        TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]

/-! ### Bialgebra instance -/

/-- The `𝔾ₐ` bialgebra instance on `R[X]`. -/
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
the unique `R`-algebra homomorphism sending `X ↦ -X`. -/
def antipodeAlgHom : R[X] →ₐ[R] R[X] :=
  Polynomial.aeval (-X : R[X])

@[simp]
theorem antipodeAlgHom_X :
    antipodeAlgHom R (X : R[X]) = -X := by
  simp [antipodeAlgHom]

@[simp]
theorem antipodeAlgHom_C (r : R) :
    antipodeAlgHom R (C r) = C r := by
  simp [antipodeAlgHom]

/-- The `𝔾ₐ` Hopf algebra instance on `R[X]` (requires `CommRing R` for the antipode
`S(X) = -X`). The antipode axiom `m ∘ (S ⊗ id) ∘ Δ = η ∘ ε` holds because both sides
send `X` to `0`: `S(X) · 1 + 1 · X = -X + X = 0 = C(ε(X))`. -/
instance instHopfAlgebra : HopfAlgebra R R[X] where
  antipode := (antipodeAlgHom R).toLinearMap
  mul_antipode_rTensor_comul := by
    have rTensor_eq : (antipodeAlgHom R).toLinearMap.rTensor R[X] =
        (Algebra.TensorProduct.map (antipodeAlgHom R)
         (AlgHom.id R R[X])).toLinearMap := by
      ext x y; simp [LinearMap.rTensor_tmul]
    dsimp only [Coalgebra.comul, Coalgebra.counit, CoalgebraStruct.comul,
          CoalgebraStruct.counit, Polynomial.instCoalgebraStruct]
    rw [rTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap,
        ← AlgHom.comp_toLinearMap, ← AlgHom.comp_toLinearMap]
    have key : (Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (antipodeAlgHom R) (AlgHom.id R R[X])).comp
           (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X])))) =
        (Algebra.ofId R R[X]).comp (Polynomial.aeval (0 : R)) :=
      Polynomial.algHom_ext (by
        simp [antipodeAlgHom,
              Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
              Algebra.ofId_apply])
    rw [key, AlgHom.comp_toLinearMap]
    ext p; simp [Algebra.linearMap_apply, Algebra.ofId_apply]
  mul_antipode_lTensor_comul := by
    have lTensor_eq : (antipodeAlgHom R).toLinearMap.lTensor R[X] =
        (Algebra.TensorProduct.map (AlgHom.id R R[X])
         (antipodeAlgHom R)).toLinearMap := by
      ext x y; simp [LinearMap.lTensor_tmul]
    dsimp only [Coalgebra.comul, Coalgebra.counit, CoalgebraStruct.comul,
          CoalgebraStruct.counit, Polynomial.instCoalgebraStruct]
    rw [lTensor_eq, ← Algebra.TensorProduct.lmul'_toLinearMap,
        ← AlgHom.comp_toLinearMap, ← AlgHom.comp_toLinearMap]
    have key : (Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (AlgHom.id R R[X]) (antipodeAlgHom R)).comp
           (Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X])))) =
        (Algebra.ofId R R[X]).comp (Polynomial.aeval (0 : R)) :=
      Polynomial.algHom_ext (by
        simp [antipodeAlgHom,
              Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
              Algebra.ofId_apply])
    rw [key, AlgHom.comp_toLinearMap]
    ext p; simp [Algebra.linearMap_apply, Algebra.ofId_apply]

end Polynomial

end
