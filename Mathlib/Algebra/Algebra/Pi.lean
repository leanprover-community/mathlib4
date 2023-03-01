/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.pi
! leanprover-community/mathlib commit b16045e4bf61c6fd619a1a68854ab3d605dcd017
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.Equiv

/-!
# The R-algebra structure on families of R-algebras

The R-algebra structure on `∀ i : I, A i` when each `A i` is an R-algebra.

## Main defintions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
-/


universe u v w

namespace Pi

variable {I : Type u}

-- The indexing type
variable {R : Type _}

-- The scalar type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

variable (I f)

instance algebra {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] :
    Algebra R (∀ i : I, f i) :=
  {
    (Pi.ringHom fun i => algebraMap R (f i) :
      R →+* ∀ i : I,
          f i) with
    commutes' := fun a f => by ext; simp [Algebra.commutes]
    smul_def' := fun a f => by ext; simp [Algebra.smul_def] }
#align pi.algebra Pi.algebra

theorem algebraMap_def {_ : CommSemiring R} [_s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) : algebraMap R (∀ i, f i) a = fun i => algebraMap R (f i) a :=
  rfl
#align pi.algebra_map_def Pi.algebraMap_def

@[simp]
theorem algebraMap_apply {_ : CommSemiring R} [_s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) (i : I) : algebraMap R (∀ i, f i) a i = algebraMap R (f i) a :=
  rfl
#align pi.algebra_map_apply Pi.algebraMap_apply

-- One could also build a `∀ i, R i`-algebra structure on `∀ i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.
variable {I} (R)

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
def evalAlgHom {_ : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }
#align pi.eval_alg_hom Pi.evalAlgHom

variable (A B : Type _) [CommSemiring R] [Semiring B] [Algebra R B]

/-- `Function.const` as an `AlgHom`. The name matches `Pi.constRingHhom`, `Pi.constMonoidHom`,
etc. -/
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }
#align pi.const_alg_hom Pi.constAlgHom

/-- When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal to that
map. -/
@[simp]
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl
#align pi.const_ring_hom_eq_algebra_map Pi.constRingHom_eq_algebraMap

@[simp]
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl
#align pi.const_alg_hom_eq_algebra_of_id Pi.constAlgHom_eq_algebra_ofId

end Pi

/-- A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this, -/
instance Function.algebra {R : Type _} (I : Type _) (A : Type _) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (I → A) :=
  Pi.algebra _ _
#align function.algebra Function.algebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {I : Type _}

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def compLeft (f : A →ₐ[R] B) (I : Type _) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }
#align alg_hom.comp_left AlgHom.compLeft

end AlgHom

namespace AlgEquiv

/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `∀ i, A₁ i` and `∀ i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.Pi_congrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
def piCongrRight {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiring R] [∀ i, Semiring (A₁ i)]
    [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  {
    @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i =>
      (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }
#align alg_equiv.Pi_congr_right AlgEquiv.piCongrRight

@[simp]
theorem piCongrRight_refl {R ι : Type _} {A : ι → Type _} [CommSemiring R] [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    (piCongrRight fun i => (AlgEquiv.refl : A i ≃ₐ[R] A i)) = AlgEquiv.refl :=
  rfl
#align alg_equiv.Pi_congr_right_refl AlgEquiv.piCongrRight_refl

@[simp]
theorem piCongrRight_symm {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align alg_equiv.Pi_congr_right_symm AlgEquiv.piCongrRight_symm

@[simp]
theorem piCongrRight_trans {R ι : Type _} {A₁ A₂ A₃ : ι → Type _} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)] [∀ i, Algebra R (A₁ i)]
    [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)] (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i)
    (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i => (e₁ i).trans (e₂ i) :=
  rfl
#align alg_equiv.Pi_congr_right_trans AlgEquiv.piCongrRight_trans

end AlgEquiv
