/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Hom

#align_import algebra.algebra.prod from "leanprover-community/mathlib"@"28aa996fc6fb4317f0083c4e6daf79878d81be33"

/-!
# The R-algebra structure on products of R-algebras

The R-algebra structure on `(i : I) → A i` when each `A i` is an R-algebra.

## Main definitions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
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
      -- ⊢ ↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑src✝) 0 = 0), map …
      dsimp
      -- ⊢ (↑(algebraMap R A) r * a, ↑(algebraMap R B) r * b) = (a * ↑(algebraMap R A)  …
      rw [commutes r a, commutes r b]
      -- 🎉 no goals
    smul_def' := by
      rintro r ⟨a, b⟩
      -- ⊢ r • (a, b) = ↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑src✝ …
      dsimp
      -- ⊢ (r • a, r • b) = (↑(algebraMap R A) r * a, ↑(algebraMap R B) r * b)
      rw [Algebra.smul_def r a, Algebra.smul_def r b] }
      -- 🎉 no goals
#align prod.algebra Prod.algebra

variable {R A B}

@[simp]
theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl
#align prod.algebra_map_apply Prod.algebraMap_apply

end Prod

namespace AlgHom

variable (R A B)

/-- First projection as `AlgHom`. -/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun _r => rfl }
#align alg_hom.fst AlgHom.fst

/-- Second projection as `AlgHom`. -/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun _r => rfl }
#align alg_hom.snd AlgHom.snd

variable {R A B}

/-- The `Pi.prod` of two morphisms is a morphism. -/
@[simps!]
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }
#align alg_hom.prod AlgHom.prod

theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align alg_hom.coe_prod AlgHom.coe_prod

@[simp]
theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (fst R B C).comp (prod f g) = f := by ext; rfl
                                                                                         -- ⊢ ↑(comp (fst R B C) (prod f g)) x✝ = ↑f x✝
                                                                                              -- 🎉 no goals
#align alg_hom.fst_prod AlgHom.fst_prod

@[simp]
theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (snd R B C).comp (prod f g) = g := by ext; rfl
                                                                                         -- ⊢ ↑(comp (snd R B C) (prod f g)) x✝ = ↑g x✝
                                                                                              -- 🎉 no goals
#align alg_hom.snd_prod AlgHom.snd_prod

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  FunLike.coe_injective Pi.prod_fst_snd
#align alg_hom.prod_fst_snd AlgHom.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C)
    where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by ext <;> rfl
                   -- ⊢ ↑((fun f => (comp (fst R B C) f, comp (snd R B C) f)) ((fun f => prod f.fst  …
                           -- 🎉 no goals
                           -- 🎉 no goals
  right_inv f := by ext <;> rfl
                    -- ⊢ (↑((fun f => prod f.fst f.snd) ((fun f => (comp (fst R B C) f, comp (snd R B …
                            -- 🎉 no goals
                            -- 🎉 no goals
#align alg_hom.prod_equiv AlgHom.prodEquiv

end AlgHom
