/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard Hill
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Derivation.Basic
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

noncomputable section

namespace Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R]

/-- `Polynomial.derivative` as a derivation. -/
@[simps]
def derivative' : Derivation R R[X] R[X] where
  toFun := derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

@[simp]
theorem derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂ :=
  Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) <| by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

variable [IsScalarTower R (Polynomial R) A]
variable (R)

/-- The derivation on `R[X]` that takes the value `a` on `X`. -/
def mkDerivation : A →ₗ[R] Derivation R R[X] A where
  toFun := fun a ↦ (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b ↦ by ext; simp
  map_smul' := fun t a ↦ by ext; simp

lemma mkDerivation_apply (a : A) (f : R[X]) :
    mkDerivation R a f = derivative f • a := by
  rfl

@[simp]
theorem mkDerivation_X (a : A) : mkDerivation R a X = a := by simp [mkDerivation_apply]

lemma mkDerivation_one_eq_derivative' : mkDerivation R (1 : R[X]) = derivative' := by
  ext : 1
  simp [derivative']

lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  rw [mkDerivation_one_eq_derivative']
  rfl

/-- `Polynomial.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }

@[simp] lemma mkDerivationEquiv_apply (a : A) :
    mkDerivationEquiv R a = mkDerivation R a := by
  rfl

@[simp] lemma mkDerivationEquiv_symm_apply (D : Derivation R R[X] A) :
    (mkDerivationEquiv R).symm D = D X := rfl

end CommSemiring
end Polynomial

namespace Derivation

open Polynomial Module

section compAEval

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

/--
For a derivation `d : A → M` and an element `a : A`, `d.compAEval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `Module.AEval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
/-
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an algebra instance
within the definition.
-/
@[simps]
def compAEval : Derivation R R[X] <| AEval R M a where
  toFun f          := AEval.of R M a (d (aeval a f))
  map_add'         := by simp
  map_smul'        := by simp
  leibniz'         := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in the `R[X]`-module `Module.AEval R M a`.
  For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  rw [← mkDerivation_apply]
  congr
  apply derivation_ext
  simp

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in `M`. For the same equation in `Module.AEval R M a`,
  see `Derivation.compAEval_eq`.
-/
theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

end compAEval

section coeffwise

variable {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

def coeffwise : Derivation R A[X] (PolynomialModule A M) :=
  Derivation.mk' ({
    toFun := fun x ↦ x.sum fun n v ↦ PolynomialModule.single A n (d v)
    map_add' := fun a b ↦ by
      dsimp only
      apply sum_add_index <;> simp
    map_smul' := fun a b ↦ by
      dsimp only [RingHom.id_apply]
      rw [sum_smul_index']
      simp only [map_smul, Polynomial.smul_sum]
      congr
      ext i c
      let val : M →ₗ[R] PolynomialModule A M := (PolynomialModule.lsingle A i).restrictScalars R
      change val (a • d c) = a • val (d c)
      apply LinearMapClass.map_smul
      simp
  }) (fun a b ↦ by
    induction a using Polynomial.induction_on' with
    | h_add _ _ h1 h2 =>
      simp only [add_mul, add_smul, smul_add, LinearMap.map_add, h1, h2]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      abel
    | h_monomial m a =>
    induction b using Polynomial.induction_on' with
    | h_add _ _ h1 h2 =>
      simp only [mul_add, add_smul, smul_add, LinearMap.map_add, h1, h2]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      abel
    | h_monomial m2 b =>
    simp only [monomial_mul_monomial, LinearMap.coe_mk, AddHom.coe_mk, map_zero, sum_monomial_index,
      leibniz, map_add, PolynomialModule.monomial_smul_single]
    ring_nf
  )

lemma coeffwise_apply (p : A[X]) :
    d.coeffwise p = p.sum fun n v ↦ (PolynomialModule.single A n) (d v) := rfl

theorem apply_aeval_eq (x : A) (p : A[X]) :
    d (aeval x p) = PolynomialModule.eval x (d.coeffwise p) + aeval x (derivative p) • d x := by
  induction p using Polynomial.induction_on' with
  | h_add => simp_all only [map_add, add_smul]; abel
  | h_monomial =>
  simp only [aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply, leibniz, leibniz_pow,
    coeffwise_apply, map_zero, sum_monomial_index, PolynomialModule.eval_single,
    derivative_monomial, map_mul, _root_.map_natCast]
  rw [add_comm, ← smul_smul, ← smul_smul, ← nsmul_eq_smul_cast]

end coeffwise

end Derivation
