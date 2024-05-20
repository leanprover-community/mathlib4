/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

#align_import category_theory.monoidal.discrete from "leanprover-community/mathlib"@"8a0e71287eb4c80e87f72e8c174835f360a6ddd9"

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/


universe u u'

open CategoryTheory Discrete MonoidalCategory

variable (M : Type u) [Monoid M]

namespace CategoryTheory

@[to_additive (attr := simps tensorObj_as leftUnitor rightUnitor associator) Discrete.addMonoidal]
instance Discrete.monoidal : MonoidalCategory (Discrete M) where
  tensorUnit := Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by dsimp; rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by dsimp; rw [eq_of_hom f])
  tensorHom f g := eqToHom (by dsimp; rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Discrete.eqToIso (mul_one X.as)
  associator X Y Z := Discrete.eqToIso (mul_assoc _ _ _)
#align category_theory.discrete.monoidal CategoryTheory.Discrete.monoidal
#align category_theory.discrete.add_monoidal CategoryTheory.Discrete.addMonoidal

@[to_additive (attr := simp) Discrete.addMonoidal_tensorUnit_as]
lemma Discrete.monoidal_tensorUnit_as : (𝟙_ (Discrete M)).as = 1 := rfl

variable {M} {N : Type u'} [Monoid N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive (attr := simps) Discrete.addMonoidalFunctor]
def Discrete.monoidalFunctor (F : M →* N) : MonoidalFunctor (Discrete M) (Discrete N) where
  obj X := Discrete.mk (F X.as)
  map f := Discrete.eqToHom (DFunLike.congr_arg F (eq_of_hom f))
  ε := Discrete.eqToHom F.map_one.symm
  μ X Y := Discrete.eqToHom (F.map_mul X.as Y.as).symm
#align category_theory.discrete.monoidal_functor CategoryTheory.Discrete.monoidalFunctor
#align category_theory.discrete.add_monoidal_functor CategoryTheory.Discrete.addMonoidalFunctor

/-- An additive morphism between add_monoids gives a
monoidal functor between the corresponding discrete monoidal categories. -/
add_decl_doc Discrete.addMonoidalFunctor

variable {K : Type u} [Monoid K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Discrete.addMonoidalFunctorComp
      "The monoidal natural isomorphism corresponding to\ncomposing two additive morphisms."]
def Discrete.monoidalFunctorComp (F : M →* N) (G : N →* K) :
    Discrete.monoidalFunctor F ⊗⋙
      Discrete.monoidalFunctor G ≅ Discrete.monoidalFunctor (G.comp F) where
  hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.discrete.monoidal_functor_comp CategoryTheory.Discrete.monoidalFunctorComp
#align category_theory.discrete.add_monoidal_functor_comp CategoryTheory.Discrete.addMonoidalFunctorComp

end CategoryTheory
