/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Monoidal functors induced on sheaves
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Functor

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section

variable {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) [J.PreservesSheafification F] [HasWeakSheafify J A] [HasWeakSheafify J B]
    [MonoidalCategory A] [MonoidalCategory B] [F.Monoidal]
    [(J.W (A := A)).IsMonoidal] [(J.W (A := B)).IsMonoidal]

attribute [local instance] monoidalCategory

noncomputable instance : (presheafToSheaf _ _ ⋙ composeAndSheafify J F).Monoidal :=
  Functor.Monoidal.transport (presheafToSheafCompComposeAndSheafifyIso J F).symm

noncomputable instance : Localization.Lifting (presheafToSheaf J A) J.W
    (presheafToSheaf _ _ ⋙ composeAndSheafify J F) (composeAndSheafify J F) where
  iso := Iso.refl _

noncomputable instance : (composeAndSheafify J F).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (presheafToSheaf _ _) J.W (composeAndSheafify J F)
    (presheafToSheaf _ _ ⋙ composeAndSheafify J F)

end

section

variable {A : Type*} [Category A]
    (F : Type (max u v) ⥤ A) [J.PreservesSheafification F] [HasWeakSheafify J A]
    [MonoidalCategory A] [F.Monoidal]
    [(J.W (A := A)).IsMonoidal]

noncomputable instance :
    letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
    (presheafToSheaf _ _ ⋙ composeAndSheafify J F).Monoidal :=
  letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
  Functor.Monoidal.transport (presheafToSheafCompComposeAndSheafifyIso J F).symm

noncomputable instance composeAndSheafifyMonoidalOfTypes :
    letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
    (composeAndSheafify J F).Monoidal := by
  letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
  exact
    Functor.Monoidal.instComp (sheafToPresheaf J (Type (max u v)))
      ((Functor.whiskeringRight Cᵒᵖ (Type (max u v)) A).obj F ⋙ presheafToSheaf J A)

end

end CategoryTheory.Sheaf
