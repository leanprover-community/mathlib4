/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.Prod

/-!
# The R-algebra structure on products of R-algebras

The R-algebra structure on `(i : I) → A i` when each `A i` is an R-algebra.

## Main definitions

* `Prod.algebra`
* `AlgHom.fst`
* `AlgHom.snd`
* `AlgHom.prod`
-/


variable {R A B C : Type*}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

namespace Prod

variable (R A B)

open Algebra

instance algebra : Algebra R (A × B) :=
  { Prod.instModule,
    RingHom.prod (algebraMap R A) (algebraMap R B) with
    commutes' := by
      rintro r ⟨a, b⟩
      dsimp
      rw [commutes r a, commutes r b]
    smul_def' := by
      rintro r ⟨a, b⟩
      dsimp
      rw [Algebra.smul_def r a, Algebra.smul_def r b] }

variable {R A B}

@[simp]
theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl

end Prod

namespace AlgHom

variable (R A B)

/-- First projection as `AlgHom`. -/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun _r => rfl }

/-- Second projection as `AlgHom`. -/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun _r => rfl }

variable {R A B}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }

theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (fst R B C).comp (prod f g) = f := by ext; rfl

@[simp]
theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (snd R B C).comp (prod f g) = g := by ext; rfl

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl

/-- `Prod.map` of two algebra homomorphisms. -/
def prodMap {D : Type*} [Semiring D] [Algebra R D] (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    A × C →ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by simp [commutes] }

end AlgHom
