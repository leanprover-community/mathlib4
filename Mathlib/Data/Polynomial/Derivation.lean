/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard Hill
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Tower
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/
noncomputable section

namespace Polynomial

open scoped BigOperators

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


end Polynomial


open Polynomial

section eval₂

universe u
variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

lemma eval₂_smul' (r : R) (f : R[X]) :
    (r • f).eval₂ (algebraMap R A) a = r • f.eval₂ (algebraMap R A) a := by
  rw [eval₂_smul, Algebra.smul_def]

/--
Suppose `A` is an `R`-algebra.
For an `A`-module `M` and an element `a : A`, `eval₂PullbackModule M a`
is the `R[X]`-module, where the action of `X` if given by multiplication by `a`.
More generally, the action of `f : R[X]` is given by `f • m = f(a) • m`.
-/
def eval₂PullbackModule (M: Type u) := Function.const A M
instance : AddCommMonoid <| eval₂PullbackModule M a := by assumption
instance : Module R[X] <| eval₂PullbackModule M a :=
  Module.compHom M <| eval₂RingHom (algebraMap R A) a
instance : Module A <| eval₂PullbackModule M a := by assumption
instance : Module R <| eval₂PullbackModule M a := by assumption
instance : IsScalarTower R A <| eval₂PullbackModule M a := by assumption
lemma eval₂PullbackModule_smul_eq (f : R[X]) (a : A) (m : eval₂PullbackModule M a) :
    f • m = (eval₂ (algebraMap R A) a f) • m := by rfl
instance : IsScalarTower R R[X] <| eval₂PullbackModule M a where
  smul_assoc r f m := by
    rw [eval₂PullbackModule_smul_eq, eval₂PullbackModule_smul_eq, eval₂_smul', smul_assoc]
lemma eval₂PullbackModule_def : eval₂PullbackModule M a = M := rfl

namespace Derivation

/--
For a derivation `d : A → M` and an element `a : A`, `d.comp_eval₂ a` is the
derivation `R[X] → M` which takes a polynomial `f` to `d (f a)`.

Here `M` is regarded as an `R[X]`-module, with the action of `f` defined
by `f • m = f(a) • m`.
-/
def comp_eval₂ : Derivation R R[X] <| eval₂PullbackModule M a where
    toFun            := d ∘ (eval₂RingHom (algebraMap R A) a)
    map_add'         := by simp
    map_smul' _ _    := by dsimp; rw [eval₂_smul', d.map_smul]
    leibniz' _ _     := by
        dsimp
        rw [eval₂_mul, d.leibniz, eval₂PullbackModule_smul_eq, eval₂PullbackModule_smul_eq]
    map_one_eq_zero' := by simp

lemma comp_eval₂_def (d : Derivation R A M) (f : R[X]) :
    d.comp_eval₂ a f = d (f.eval₂ (algebraMap R A) a) := by rfl

lemma comp_eval₂_eq (d : Derivation R A <| eval₂PullbackModule M a) (f : R[X]) :
    d.comp_eval₂ a f = f.derivative.eval₂ (algebraMap R A) a • d a := by
  rw [←eval₂PullbackModule_smul_eq, ←mkDerivation_apply]
  congr
  apply derivation_ext
  rw [comp_eval₂_def, eval₂_X, mkDerivation_X (R := R)]

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have

    `d(f(a)) = f.derivative (a) * d a`.
-/
theorem eval₂ (d : Derivation R A M) (f : R[X]) :
    d (f.eval₂ (algebraMap R A) a) = f.derivative.eval₂ (algebraMap R A) a • d a :=
  comp_eval₂_eq a d f

theorem aeval (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  comp_eval₂_eq a d f

end Derivation
end eval₂
