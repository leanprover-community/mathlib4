/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Category.Cat

import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Bicategory.Coherence


/-!
# 2-Yoneda embedding

-/

namespace CategoryTheory

open Category Bicategory Bicategory.Opposite

open Bicategory

universe w₁ v₁ u₁ w v u

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev LocallySmallBicategory (B : Type u₁) : Type _ := Bicategory.{v₁, v₁, u₁} B

namespace Bicategory

open NatTrans

-- TODO: small when?!
variable {B : Type u₁} [LocallySmallBicategory.{v₁} B]

-- TODO: need more simps?
@[simps]
def representable (x : B) : Pseudofunctor Bᴮᵒᵖ Cat.{v₁, v₁} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of ((bop x) ⟶ y))
  -- TODO: did postcomposing to avoid having to take "bop" of the functor
      (fun a b => (postcomposing (bop x) a b))
  mapId := fun a => rightUnitorNatIso (bop x) a
  mapComp := fun {a b c} f g => (associatorNatIsoLeft (bop x) f g).symm
  map₂_whisker_left := by
    intro a b c f g h η
    apply NatTrans.ext
    ext x
    -- TODO: why doesn't simp do this
    rw [NatTrans.comp_app, NatTrans.comp_app]
    dsimp
    simp
  map₂_whisker_right := by
    intro a b c f g h η
    apply NatTrans.ext
    ext x
    rw [NatTrans.comp_app, NatTrans.comp_app]
    dsimp
    simp
  map₂_associator := by
    intro a b c d f g h
    apply NatTrans.ext
    ext i
    dsimp
    simp only [Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, id_comp]
    -- TODO: need to do this twice more..
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    dsimp
    rw [Iso.eq_inv_comp, ← pentagon_inv_hom_hom_hom_hom]
  map₂_left_unitor := by
    intro a b f
    apply NatTrans.ext
    ext x
    dsimp
    simp
    rw [NatTrans.comp_app]
    simp [← triangle_assoc_comp_right]
  map₂_right_unitor := by
    intro a b f
    apply NatTrans.ext
    ext x
    dsimp
    simp
    rw [NatTrans.comp_app]
    simp [← triangle_assoc_comp_left]

-- Could this be representable from normal coyoneda?
@[simps?]
def StrongNatTrans.representable {x y : B} (f : x ⟶ y) : representable x ⟶ representable y where
  app z := (precomp z f.bop)
  naturality {a b} g := {
    hom := { app := fun h => (α_ f.bop h g).inv }
    inv := { app := fun h => (α_ f.bop h g).hom }
    hom_inv_id := by
      -- this all should be automatic
      apply NatTrans.ext; ext x
      rw [NatTrans.comp_app, NatTrans.id_app]
      simp
    inv_hom_id := by
      -- this all should be automatic
      apply NatTrans.ext; ext x
      rw [NatTrans.comp_app, NatTrans.id_app]
      simp
  }

-- TODO: invertible if f is?
@[simps?]
def Modification.representable {x y : B} {f g : x ⟶ y} (η : f ⟶ g) :
    OplaxNatTrans.Modification (StrongNatTrans.representable f).toOplax
      (StrongNatTrans.representable g).toOplax where
  -- should this be expressed in terms of precomposing somewhere?
  app a := {
    app := ((bop2 η) ▷ ·)
      -- TODO: rw suggested some yoneda here... Can yoneda be used higher up
      -- here somewhere?
    naturality := by intros; apply whisker_exchange
  }
  naturality h := by
    apply NatTrans.ext; ext x
    rw [NatTrans.comp_app, NatTrans.comp_app]
    apply associator_inv_naturality_left

@[simps]
def yoneda.prelaxFunctor : PrelaxFunctor B (Pseudofunctor Bᴮᵒᵖ Cat.{v₁, v₁}) where
  obj x := representable x
  map f := StrongNatTrans.representable f
  map₂ η := Modification.representable η
  map₂_id := by
    intros
    dsimp
    apply OplaxNatTrans.ext
    intro c
    -- some API is missing here
    sorry
  map₂_comp := by
    intros
    dsimp
    apply OplaxNatTrans.ext
    intro c
    -- some API is missing here
    sorry

def yoneda : Pseudofunctor B (Pseudofunctor Bᴮᵒᵖ Cat.{v₁, v₁}) where
  toPrelaxFunctor := yoneda.prelaxFunctor
  -- maybe som mkOfIso here?
  -- TODO: just look it up in the notes
  mapId a :=
  {
    hom := {
      -- at this point should be rightUnitor?
      app := fun b => by dsimp; apply leftUnitor _
      naturality := sorry
    }
    inv := sorry
    hom_inv_id := sorry
    inv_hom_id := sorry
  }
  mapComp := sorry
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

end Bicategory

end CategoryTheory
