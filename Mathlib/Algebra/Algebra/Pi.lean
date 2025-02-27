/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Equiv

/-!
# The R-algebra structure on families of R-algebras

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main definitions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
-/

namespace Pi

-- The indexing type
variable (ι : Type*)

-- The scalar type
variable {R : Type*}

-- The family of types already equipped with instances
variable (A : ι → Type*)
variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

instance algebra : Algebra R (Π i, A i) where
  algebraMap := Pi.ringHom fun i ↦ algebraMap R (A i)
  commutes' := fun a f ↦ by ext; simp [Algebra.commutes]
  smul_def' := fun a f ↦ by ext; simp [Algebra.smul_def]

theorem algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i ↦ algebraMap R (A i) a :=
  rfl

@[simp]
theorem algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMap R (A i) a :=
  rfl

variable {ι} (R)

/-- A family of algebra homomorphisms `g i : B →ₐ[R] A i` defines a ring homomorphism
`Pi.algHom g : B →ₐ[R] Π i, A i` given by `Pi.algHom g x i = g i x`. -/
@[simps!]
def algHom {B : Type*} [Semiring B] [Algebra R B] (g : ∀ i, B →ₐ[R] A i) : B →ₐ[R] Π i, A i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
def evalAlgHom (i : ι) : (Π i, A i) →ₐ[R] A i :=
  { Pi.evalRingHom A i with
    toFun := fun f ↦ f i
    commutes' := fun _ ↦ rfl }

@[simp]
theorem algHom_evalAlgHom : algHom R A (evalAlgHom R A) = AlgHom.id R (Π i, A i) := rfl

/-- `Pi.algHom` commutes with composition. -/
theorem algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : ∀ i, C →ₐ[R] A i) (h : B →ₐ[R] C) :
    (algHom R A g).comp h = algHom R A (fun i ↦ (g i).comp h) := rfl

variable (S : ι → Type*) [∀ i, CommSemiring (S i)]

instance [∀ i, Algebra (S i) (A i)] : Algebra (Π i, S i) (Π i, A i) where
  algebraMap := Pi.ringHom fun _ ↦ (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := funext fun _ ↦ Algebra.smul_def _ _

example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

variable (A B : Type*) [Semiring B] [Algebra R B]

/-- `Function.const` as an `AlgHom`. The name matches `Pi.constRingHom`, `Pi.constMonoidHom`,
etc. -/
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ ↦ rfl }

/-- When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal to that
map. -/
@[simp]
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl

@[simp]
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl

end Pi

/-- A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (ι → A) :=
  Pi.algebra _ _

namespace AlgHom

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `ι → A` and `ι → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def compLeft (f : A →ₐ[R] B) (ι : Type*) : (ι → A) →ₐ[R] ι → B :=
  { f.toRingHom.compLeft ι with
    toFun := fun h ↦ f ∘ h
    commutes' := fun c ↦ by
      ext
      exact f.commutes' c }

end AlgHom

namespace AlgEquiv

variable {R ι : Type*} {A₁ A₂ A₃ : ι → Type*}
variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]
variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
def piCongrRight (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i ↦ (e i).toRingEquiv with
    toFun := fun x j ↦ e j (x j)
    invFun := fun x j ↦ (e j).symm (x j)
    commutes' := fun r ↦ by
      ext i
      simp }

@[simp]
theorem piCongrRight_refl :
    (piCongrRight fun i ↦ (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl :=
  rfl

@[simp]
theorem piCongrRight_symm (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i ↦ (e i).symm :=
  rfl

@[simp]
theorem piCongrRight_trans (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i ↦ (e₁ i).trans (e₂ i) :=
  rfl

end AlgEquiv
