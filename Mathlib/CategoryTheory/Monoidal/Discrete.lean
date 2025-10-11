/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/


universe u u'

open CategoryTheory Discrete MonoidalCategory

variable (M : Type u)

namespace CategoryTheory

@[simps tensorObj_as leftUnitor rightUnitor associator]
instance Discrete.monoidal [Monoid M] : MonoidalCategory (Discrete M) where
  tensorUnit := Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Discrete.eqToIso (mul_one X.as)
  associator _ _ _ := Discrete.eqToIso (mul_assoc _ _ _)

@[simps tensorObj_as leftUnitor rightUnitor associator]
instance Discrete.addMonoidal [AddMonoid M] : MonoidalCategory (Discrete M) where
  tensorUnit := Discrete.mk 0
  tensorObj X Y := Discrete.mk (X.as + Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (zero_add X.as)
  rightUnitor X := Discrete.eqToIso (add_zero X.as)
  associator _ _ _ := Discrete.eqToIso (add_assoc _ _ _)

@[simp]
lemma Discrete.monoidal_tensorUnit_as [Monoid M] : (𝟙_ (Discrete M)).as = 1 := rfl

@[simp]
lemma Discrete.addMonoidal_tensorUnit_as [AddMonoid M] : (𝟙_ (Discrete M)).as = 0 := rfl

section Monoid

variable [Monoid M]

variable {M} {N : Type u'} [Monoid N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
def Discrete.monoidalFunctor (F : M →* N) : Discrete M ⥤ Discrete N :=
  Discrete.functor (fun X ↦ Discrete.mk (F X))

@[simp]
lemma Discrete.monoidalFunctor_obj (F : M →* N) (m : M) :
    (Discrete.monoidalFunctor F).obj (Discrete.mk m) = Discrete.mk (F m) := rfl

instance Discrete.monoidalFunctorMonoidal (F : M →* N) :
    (Discrete.monoidalFunctor F).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_one.symm
        μIso := fun m₁ m₂ ↦ Discrete.eqToIso (F.map_mul _ _).symm }

open Functor.LaxMonoidal Functor.OplaxMonoidal

lemma Discrete.monoidalFunctor_ε (F : M →* N) :
    ε (monoidalFunctor F) = Discrete.eqToHom F.map_one.symm := rfl

lemma Discrete.monoidalFunctor_η (F : M →* N) :
    η (monoidalFunctor F) = Discrete.eqToHom F.map_one := rfl

lemma Discrete.monoidalFunctor_μ (F : M →* N) (m₁ m₂ : Discrete M) :
    μ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _).symm := rfl

lemma Discrete.monoidalFunctor_δ (F : M →* N) (m₁ m₂ : Discrete M) :
    δ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _) := rfl

-- /-- An additive morphism between add_monoids gives a
-- monoidal functor between the corresponding discrete monoidal categories. -/
-- add_decl_doc Discrete.addMonoidalFunctor

variable {K : Type u} [Monoid K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
def Discrete.monoidalFunctorComp (F : M →* N) (G : N →* K) :
    Discrete.monoidalFunctor F ⋙ Discrete.monoidalFunctor G ≅
      Discrete.monoidalFunctor (G.comp F) := Iso.refl _

instance Discrete.monoidalFunctorComp_isMonoidal (F : M →* N) (G : N →* K) :
    NatTrans.IsMonoidal (Discrete.monoidalFunctorComp F G).hom where
  unit := by
    dsimp only [comp_ε, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_μ]
    simp [eqToHom_map]

end Monoid

section AddMonoid

variable [AddMonoid M]

variable {M} {N : Type u'} [AddMonoid N]

/-- An additive morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
def Discrete.addMonoidalFunctor (F : M →+ N) : Discrete M ⥤ Discrete N :=
  Discrete.functor (fun X ↦ Discrete.mk (F X))

@[simp]
lemma Discrete.addMonoidalFunctor_obj (F : M →+ N) (m : M) :
    (Discrete.addMonoidalFunctor F).obj (Discrete.mk m) = Discrete.mk (F m) := rfl

instance Discrete.addMonoidalFunctorMonoidal (F : M →+ N) :
    (Discrete.addMonoidalFunctor F).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_zero.symm
        μIso := fun m₁ m₂ ↦ Discrete.eqToIso (F.map_add _ _).symm }

open Functor.LaxMonoidal Functor.OplaxMonoidal

lemma Discrete.addMonoidalFunctor_ε (F : M →+ N) :
    ε (addMonoidalFunctor F) = Discrete.eqToHom F.map_zero.symm := rfl

lemma Discrete.addMonoidalFunctor_η (F : M →+ N) :
    η (addMonoidalFunctor F) = Discrete.eqToHom F.map_zero := rfl

lemma Discrete.addMonoidalFunctor_μ (F : M →+ N) (m₁ m₂ : Discrete M) :
    μ (addMonoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_add _ _).symm := rfl

lemma Discrete.addMonoidalFunctor_δ (F : M →+ N) (m₁ m₂ : Discrete M) :
    δ (addMonoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_add _ _) := rfl

variable {K : Type u} [AddMonoid K]

/-- An additive morphism between add_monoids gives a
monoidal functor between the corresponding discrete monoidal categories. -/
def Discrete.addMonoidalFunctorComp (F : M →+ N) (G : N →+ K) :
    Discrete.addMonoidalFunctor F ⋙ Discrete.addMonoidalFunctor G ≅
      Discrete.addMonoidalFunctor (G.comp F) := Iso.refl _

instance Discrete.addMonoidalFunctorComp_isMonoidal (F : M →+ N) (G : N →+ K) :
    NatTrans.IsMonoidal (Discrete.addMonoidalFunctorComp F G).hom where
  unit := by
    dsimp only [comp_ε, addMonoidalFunctorComp, Iso.refl, Discrete.addMonoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, addMonoidalFunctorComp, Iso.refl, Discrete.addMonoidalFunctor_μ]
    simp [eqToHom_map]

end AddMonoid

end CategoryTheory
