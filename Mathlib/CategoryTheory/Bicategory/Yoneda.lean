/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
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

-- TODO: some API need to be added to prelax refactor

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

#check Cat.comp_app

attribute [local simp] Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app

-- TODO: most lemmas should be automatic if I add local simp lemmas
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
  naturality {a b} g := {
    hom := Cat.NatTrans.mk' fun h ↦ (α_ f.op h g).inv
    inv := Cat.NatTrans.mk' fun h ↦ (α_ f.op h g).hom }

-- TODO: invertible if f is?
@[simps]
def Modification.representable {x y : B} {f g : x ⟶ y} (η : f ⟶ g) :
    Modification (StrongNatTrans.representable f) (StrongNatTrans.representable g) where
  -- should this be expressed in terms of precomposing somewhere?
  app a := {
    app := ((op2 η) ▷ ·)
      -- TODO: rw suggested some yoneda here... Can yoneda be used higher up
      -- here somewhere?
    naturality := by intros; apply whisker_exchange
  }
  naturality h := by
    ext x
    apply associator_inv_naturality_left

@[simps]
def yoneda.prelaxFunctor : PrelaxFunctor B (Pseudofunctor Bᵒᵖ Cat.{v₁, v₁}) where
  obj x := representable x
  map f := StrongNatTrans.representable f
  map₂ η := Modification.representable η

def yoneda : Pseudofunctor B (Pseudofunctor Bᵒᵖ Cat.{v₁, v₁}) where
  toPrelaxFunctor := yoneda.prelaxFunctor
  mapId a := isoMk (fun b => leftUnitorNatIso (op a) b)
  mapComp f g := isoMk
      (fun b ↦ associatorNatIsoRight _ _ b)
        <| by
    intro a b h
    ext x
    simp
    erw [pentagon_hom_inv_inv_inv_hom g.op f.op x h] -- TODO. simp lemma so should be automatic
    rfl
  -- these should all be proven generally?
  map₂_whisker_left := by
    intros a b c f g h η
    ext d x
    simp
    slice_rhs 2 4 =>
      rw [associator_naturality_left, ← assoc, Iso.inv_hom_id, id_comp]
    sorry -- almost done...!
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

end Bicategory

end CategoryTheory
