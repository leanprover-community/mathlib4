/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.CategoryTheory.Yoneda

/-!
# Yoneda embeddings

This file defines a few Yoneda embeddings for the category of commutative groups.
-/

open CategoryTheory

universe u

/-- The `CommGrpCat`-valued coyoneda embedding. -/
@[to_additive (attr := simps) /-- The `AddCommGrpCat`-valued coyoneda embedding. -/]
def CommGrpCat.coyoneda : CommGrpCatᵒᵖ ⥤ CommGrpCat ⥤ CommGrpCat where
  obj M := { obj N := of (M.unop →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

/-- The `CommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommGrpCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
def CommGrpCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ { hom f := ofHom f, inv f := f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommGrpCat`-valued presheaves of commutative
groups. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommGrpCat`-valued presheaves of commutative
groups. -/]
def CommGrpCat.coyonedaType : (Type u)ᵒᵖ ⥤ CommGrpCat.{u} ⥤ CommGrpCat.{u} where
  obj X := { obj G := of <| X.unop → G
             map f := ofHom <| Pi.monoidHom fun i ↦ f.hom.comp <| Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ <| f.unop i }
