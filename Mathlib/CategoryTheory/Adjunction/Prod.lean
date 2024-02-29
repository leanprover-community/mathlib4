/-
Copyright (c) 2020 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Products of adjunction

Given a pair of adjunction `F₁ ⊣ G₁`, `F₂ ⊣ G₂` there is an adjunction of
products `F₁.prod F₂ ⊣ G₁.prod G₂`.

-/

open CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

open CategoryTheory.Category
open CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable
  {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]
  {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : C ⥤ D} {G₂ : D ⥤ C}

/-- The cartesian product of two adjunctions. -/
@[simps!]
def prod (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) : F₁.prod F₂ ⊣ G₁.prod G₂ where
  homEquiv XY ZW := .prodCongr (adj₁.homEquiv XY.1 ZW.1) (adj₂.homEquiv XY.2 ZW.2)
  -- we're using a defeq 𝟭 (C × D) ≅ 𝟭 C × 𝟭 D here, maybe that should be changed
  unit := NatTrans.prod adj₁.unit adj₂.unit
  counit := NatTrans.prod adj₁.counit adj₂.counit

end CategoryTheory.Adjunction
