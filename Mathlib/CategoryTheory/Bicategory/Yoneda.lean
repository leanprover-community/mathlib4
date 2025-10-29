/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Category.Cat

import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Bicategory.Coherence


/-!
# 2-Yoneda embedding

-/

namespace CategoryTheory

open Category Bicategory Bicategory.Opposite Opposite

open Bicategory Pseudofunctor StrongTrans

universe w₁ v₁ u₁ w v u

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev LocallySmallBicategory (B : Type u₁) : Type _ := Bicategory.{v₁, v₁, u₁} B

namespace Bicategory

open NatTrans

-- TODO: small when?!
variable {B : Type u₁} [LocallySmallBicategory.{v₁} B]

attribute [local simp] Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app

@[simps]
def representable (x : B) : Pseudofunctor Bᵒᵖ Cat.{v₁, v₁} where
  -- On objects:
  -- Hom functors: postcomposing (in `Bᴮᵒᵖ`).
  toPrelaxFunctor :=
    PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of ((op x) ⟶ y))
      (fun a b => (postcomposing (op x) a b))
  mapId a := rightUnitorNatIso (op x) a
  mapComp f g := (associatorNatIsoLeft (op x) f g).symm

-- Could this be representable from normal coyoneda?
@[simps]
def StrongNatTrans.representable {x y : B} (f : x ⟶ y) : representable x ⟶ representable y where
  app z := (precomp z f.op)
  naturality {a b} g := { -- TODO: Cat.NatIso.mk? Or just NatIso.mk?
    hom := Cat.NatTrans.mk' fun h ↦ (α_ f.op h g).inv
    inv := Cat.NatTrans.mk' fun h ↦ (α_ f.op h g).hom }

-- TODO:4 invertible if f is?
@[simps]
def Modification.representable {x y : B} {f g : x ⟶ y} (η : f ⟶ g) :
    Modification (StrongNatTrans.representable f) (StrongNatTrans.representable g) where
  app a := (precomposing _ _ _).map (op2 η)

@[simps]
def yoneda.prelaxFunctor : PrelaxFunctor B (Pseudofunctor Bᵒᵖ Cat.{v₁, v₁}) where
  obj x := representable x
  map f := StrongNatTrans.representable f
  map₂ η := Modification.representable η

@[simps]
def yoneda : Pseudofunctor B (Pseudofunctor Bᵒᵖ Cat.{v₁, v₁}) where
  toPrelaxFunctor := yoneda.prelaxFunctor
  mapId a := isoMk (fun b => leftUnitorNatIso (op a) b)
  mapComp f g := isoMk (fun b ↦ associatorNatIsoRight g.op f.op b)

end Bicategory

end CategoryTheory
