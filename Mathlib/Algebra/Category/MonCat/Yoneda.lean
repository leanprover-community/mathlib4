/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.CategoryTheory.Yoneda

/-!
# Yoneda embeddings

This file defines a few Yoneda embeddings for the category of commutative monoids.
-/

open CategoryTheory

universe u

/-- The `CommMonCat`-valued coyoneda embedding. -/
@[to_additive (attr := simps) /-- The `AddCommMonCat`-valued coyoneda embedding. -/]
def CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  obj M := { obj N := of (M.unop →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

/-- The `CommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/
@[to_additive (attr := simps!)
/-- The `AddCommMonCat`-valued coyoneda embedding composed with the forgetful functor is the usual
coyoneda embedding. -/]
def CommMonCat.coyonedaForget :
    coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ { hom f := ofHom f, inv f := f.hom }

/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `CommMonCat`-valued presheaves of commutative
monoids. -/
@[to_additive (attr := simps)
/-- The Hom bifunctor sending a type `X` and a commutative monoid `M` to the commutative monoid
`X → M` with pointwise operations.

This is also the coyoneda embedding of `Type` into `AddCommMonCat`-valued presheaves of commutative
monoids. -/]
def CommMonCat.coyonedaType : (Type u)ᵒᵖ ⥤ CommMonCat.{u} ⥤ CommMonCat.{u} where
  obj X := { obj M := of <| X.unop → M
             map f := ofHom <| Pi.monoidHom fun i ↦ f.hom.comp <| Pi.evalMonoidHom _ i }
  map f := { app N := ofHom <| Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ <| f.unop i }
