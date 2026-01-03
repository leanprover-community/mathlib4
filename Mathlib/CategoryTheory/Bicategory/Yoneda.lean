/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# 2-Yoneda embedding

-/

namespace CategoryTheory

open Category Bicategory Bicategory.Opposite Opposite

open Bicategory Pseudofunctor StrongTrans

universe w₁ v₁ u₁ w v u

namespace Bicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]

attribute [local simp] Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app

/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation. -/
@[simps!]
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w₁, v₁} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposing (unop b) (unop a) x)
  mapId a := leftUnitorNatIso (unop a) x
  mapComp f g := associatorNatIsoRight g.unop f.unop x

/-- Postcomposing of a 1-morhisms seen as a strong transformation between pseudofunctors. -/
@[simps!]
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposing (unop x) a b).obj f
  naturality g := (associatorNatIsoMiddle g.unop f)

/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors. -/
@[simps!]
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { app x := (postcomposing (unop x) a b).map η }

/-- The yoneda pseudofunctor from `B` to `Pseudofunctor Bᵒᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
def yoneda : Pseudofunctor B (Pseudofunctor Bᵒᵖ Cat.{w₁, v₁}) where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun x ↦ yoneda₀ x) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIso (unop b) a)
  mapComp f g := (isoMk (fun b ↦ associatorNatIsoLeft (unop b) f g)).symm

end Bicategory

end CategoryTheory
