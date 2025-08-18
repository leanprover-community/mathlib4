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

/-- The `CommGrp`-valued coyoneda embedding. -/
@[to_additive (attr := simps) /-- The `AddCommGrp`-valued coyoneda embedding. -/]
def CommGrp.coyoneda : CommGrpᵒᵖ ⥤ CommGrp ⥤ CommGrp where
  obj M := { obj N := of (M.unop →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

/-- The `CommGrp`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommGrp`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
def CommGrp.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ { hom f := ofHom f, inv f := f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommGrp`-valued presheaves of commutative
groups. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative group `G` to the commutative group
`X → G` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommGrp`-valued presheaves of commutative
groups. -/]
def CommGrp.coyonedaType : (Type u)ᵒᵖ ⥤ CommGrp.{u} ⥤ CommGrp.{u} where
  obj X := { obj G := of <| X.unop → G
             map f := ofHom <| Pi.monoidHom fun i ↦ f.hom.comp <| Pi.evalMonoidHom _ i }
  map f := { app G := ofHom <| Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ <| f.unop i }
