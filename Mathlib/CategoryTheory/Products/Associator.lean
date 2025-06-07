/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
import Mathlib.CategoryTheory.Products.Basic

/-!
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] (E : Type u₃)
  [Category.{v₃} E]

/-- The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simps]
def associator : (C × D) × E ⥤ C × D × E where
  obj X := (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => (f.1.1, (f.1.2, f.2))

/-- The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
def inverseAssociator : C × D × E ⥤ (C × D) × E where
  obj X := ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => ((f.1, f.2.1), f.2.2)

/-- The equivalence of categories expressing associativity of products of categories.
-/
@[simps]
def associativity : (C × D) × E ≌ C × D × E where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO pentagon natural transformation? ...satisfying?

variable (A : Type u₄) [Category.{v₄} A]

/-- The associator isomorphism is compatible with `prodFunctorToFunctorProd`. -/
@[simps!]
def prodFunctorToFunctorProdAssociator :
    (associativity _ _ _).functor ⋙ ((𝟭 _).prod (prodFunctorToFunctorProd A D E) ⋙
      (prodFunctorToFunctorProd A C (D × E))) ≅
        (prodFunctorToFunctorProd A C D).prod (𝟭 _) ⋙ (prodFunctorToFunctorProd A (C × D) E) ⋙
          (associativity C D E).congrRight.functor :=
  Iso.refl _

/-- The associator isomorphism is compatible with `functorProdToProdFunctor`. -/
@[simps!]
def functorProdToProdFunctorAssociator :
    (associativity _ _ _).congrRight.functor ⋙ functorProdToProdFunctor A C (D × E) ⋙
      (𝟭 _).prod (functorProdToProdFunctor A D E) ≅
        functorProdToProdFunctor A (C × D) E ⋙ (functorProdToProdFunctor A C D).prod (𝟭 _) ⋙
          (associativity _ _ _).functor :=
  Iso.refl _

end CategoryTheory.prod
