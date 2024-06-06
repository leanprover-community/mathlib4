/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

#align_import algebra.category.Module.monoidal.closed from "leanprover-community/mathlib"@"74403a3b2551b0970855e14ef5e8fd0d6af1bfc2"

/-!
# The monoidal closed structure on `Module R`.
-/

suppress_compilation

universe v w x u

open CategoryTheory Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

-- Porting note: removed @[simps] as the simpNF linter complains
/-- Auxiliary definition for the `MonoidalClosed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking. )
-/
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun f := LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f)
  invFun f := (β_ M N).hom ≫ TensorProduct.lift f
  left_inv f := by
    apply TensorProduct.ext'
    intro m n
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [coe_comp]
    rw [Function.comp_apply]
    -- This used to be `rw` and was longer (?), but we need `erw` after leanprover/lean4#2644
    erw [MonoidalCategory.braiding_hom_apply, TensorProduct.lift.tmul]
  right_inv f := rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_closed_hom_equiv ModuleCat.monoidalClosedHomEquiv

instance : MonoidalClosed (ModuleCat.{u} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                intros
                apply TensorProduct.ext'
                intro m n
                rfl } }

theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.ihom_map_apply ModuleCat.ihom_map_apply

open MonoidalCategory

-- Porting note: `CoeFun` was replaced by `DFunLike`
-- I can't seem to express the function coercion here without writing `@DFunLike.coe`.
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    @DFunLike.coe _ _ _ LinearMap.instFunLike
      ((MonoidalClosed.curry f : N →ₗ[R] M →ₗ[R] P) y) x = f (x ⊗ₜ[R] y) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_closed_curry ModuleCat.monoidalClosed_curry

@[simp]
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) =
      @DFunLike.coe _ _ _ LinearMap.instFunLike (f y) x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_closed_uncurry ModuleCat.monoidalClosed_uncurry

/-- Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.` -/
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = TensorProduct.uncurry _ _ _ _ LinearMap.id.flip := by
  apply TensorProduct.ext'
  apply ModuleCat.monoidalClosed_uncurry
set_option linter.uppercaseLean3 false in
#align Module.ihom_ev_app ModuleCat.ihom_ev_app

/-- Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in the natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`. -/
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = (TensorProduct.mk _ _ _).flip :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.ihom_coev_app ModuleCat.ihom_coev_app

theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = LinearMap.lcomp R _ f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_closed_pre_app ModuleCat.monoidalClosed_pre_app

end ModuleCat
