/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Functor.Currying

/-!
# External product of diagrams in a monoidal category

In a monoidal category `C`, given a pair of diagrams `K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, we
introduce the external product `K₁ ⊠ K₂ : J₁ × J₂ ⥤ C` as the bifunctor `(j₁, j₂) ↦ K₁ j₁ ⊗ K₂ j₂`.
The notation `- ⊠ -` is scoped to `MonoidalCategory.ExternalProduct`.
-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.MonoidalCategory
open Functor

variable (J₁ : Type u₁) (J₂ : Type u₂) (C : Type u₃)
    [Category.{v₁} J₁] [Category.{v₂} J₂] [Category.{v₃} C] [MonoidalCategory C]

/-- The (curried version of the) external product bifunctor: given diagrams
`K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, this is the bifunctor `j₁ ↦ j₂ ↦ K₁ j₁ ⊗ K₂ j₂`. -/
@[simps!]
def externalProductBifunctorCurried : (J₁ ⥤ C) ⥤ (J₂ ⥤ C) ⥤ J₁ ⥤ J₂ ⥤ C :=
  (Functor.postcompose₂.obj <| (evaluation _ _).obj <| curriedTensor C).obj <| whiskeringLeft₂ C

/-- The external product bifunctor: given diagrams
`K₁ : J₁ ⥤ C` and `K₂ : J₂ ⥤ C`, this is the bifunctor `(j₁, j₂) ↦ K₁ j₁ ⊗ K₂ j₂`. -/
@[simps!]
def externalProductBifunctor : ((J₁ ⥤ C) × (J₂ ⥤ C)) ⥤ J₁ × J₂ ⥤ C :=
  uncurry.obj <| (Functor.postcompose₂.obj <| uncurry).obj <|
    externalProductBifunctorCurried J₁ J₂ C

variable {J₁ J₂ C}
/-- An abbreviation for the action of `externalProductBifunctor J₁ J₂ C` on objects. -/
abbrev externalProduct (F₁ : J₁ ⥤ C) (F₂ : J₂ ⥤ C) :=
  externalProductBifunctor J₁ J₂ C|>.obj (F₁, F₂)

namespace ExternalProduct
/-- Notation for `externalProduct`.
Do `open scoped CategoryTheory.MonoidalCategory.ExternalProduct`
to bring this notation in scope. -/
scoped infixr:80 " ⊠ " => externalProduct

end ExternalProduct

open scoped ExternalProduct

variable (J₁ J₂ C)

/-- When both diagrams have the same source category, composing the external product with
the diagonal gives the pointwise functor tensor product.
Note that `(externalProductCompDiagIso _ _).app (F₁, F₂) : Functor.diag J₁ ⋙ F₁ ⊠ F₂ ≅ F₁ ⊗ F₂`
type checks. -/
@[simps!]
def externalProductCompDiagIso :
    externalProductBifunctor J₁ J₁ C ⋙ (whiskeringLeft _ _ _ |>.obj <| Functor.diag J₁) ≅
    tensor (J₁ ⥤ C) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp [tensorHom_def]))
    (fun _ ↦ by ext; simp [tensorHom_def])

/-- When `C` is braided, there is an isomorphism `Prod.swap _ _ ⋙ F₁ ⊠ F₂ ≅ F₂ ⊠ F₁`, natural
in both `F₁` and `F₂`.
Note that `(externalProductSwap _ _ _).app (F₁, F₂) : Prod.swap _ _ ⋙ F₁ ⊠ F₂ ≅ F₂ ⊠ F₁`
type checks. -/
@[simps!]
def externalProductSwap [BraidedCategory C] :
    externalProductBifunctor J₁ J₂ C ⋙ (whiskeringLeft _ _ _ |>.obj <| Prod.swap _ _) ≅
    Prod.swap _ _ ⋙ externalProductBifunctor J₂ J₁ C :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ β_ _ _) (by simp [whisker_exchange]))
    (fun _ ↦ by ext; simp [whisker_exchange])

/-- A version of `externalProductSwap` phrased in terms of the curried functors. -/
@[simps!]
def externalProductFlip [BraidedCategory C] :
    (Functor.postcompose₂.obj <| flipFunctor _ _ _).obj
      (externalProductBifunctorCurried J₁ J₂ C) ≅
    (externalProductBifunctorCurried J₂ J₁ C).flip :=
  NatIso.ofComponents <| fun _ ↦ NatIso.ofComponents <|
    fun _ ↦ NatIso.ofComponents <| fun _ ↦ NatIso.ofComponents (fun _ ↦ β_ _ _)

section Composition

variable {J₁ J₂ C} {I₁ : Type u₃} {I₂ : Type u₄} [Category.{v₃} I₁] [Category.{v₄} I₂]

/-- Composing `F₁ × F₂` with `G₁ ⊠ G₂` is isomorphic to `(F₁ ⋙ G₁) ⊠ (F₂ ⋙ G₂)`. -/
@[simps!]
def prodCompExternalProduct (F₁ : I₁ ⥤ J₁) (G₁ : J₁ ⥤ C) (F₂ : I₂ ⥤ J₂) (G₂ : J₂ ⥤ C) :
     F₁.prod F₂ ⋙ G₁ ⊠ G₂ ≅ (F₁ ⋙ G₁) ⊠ (F₂ ⋙ G₂) := NatIso.ofComponents (fun _ ↦ Iso.refl _)

end Composition

end CategoryTheory.MonoidalCategory
