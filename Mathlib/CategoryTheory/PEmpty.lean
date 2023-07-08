/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.pempty
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.DiscreteCategory

/-!
# The empty category

Defines a category structure on `PEmpty`, and the unique functor `PEmpty ⥤ C` for any category `C`.
-/

universe w v u
-- morphism levels before object levels. See note [CategoryTheory universes].
namespace CategoryTheory

namespace Functor

variable (C : Type u) [Category.{v} C]

/-- Equivalence between two empty categories. -/
def emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty where
  functor :=
    { obj := PEmpty.elim ∘ Discrete.as
      map := fun {X} _ _ => X.as.elim }
  inverse :=
    { obj := PEmpty.elim ∘ Discrete.as
      map := fun {X} _ _ => X.as.elim }
  unitIso :=
    { hom := { app := fun X => X.as.elim }
      inv := { app := fun X => X.as.elim } }
  counitIso :=
    { hom := { app := fun X => X.as.elim }
      inv := { app := fun X => X.as.elim } }
#align category_theory.functor.empty_equivalence CategoryTheory.Functor.emptyEquivalence

/-- The canonical functor out of the empty category. -/
def empty : Discrete.{w} PEmpty ⥤ C :=
  Discrete.functor PEmpty.elim
#align category_theory.functor.empty CategoryTheory.Functor.empty

variable {C}

/-- Any two functors out of the empty category are isomorphic. -/
def emptyExt (F G : Discrete.{w} PEmpty ⥤ C) : F ≅ G :=
  Discrete.natIso fun x => x.as.elim
#align category_theory.functor.empty_ext CategoryTheory.Functor.emptyExt

/-- Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def uniqueFromEmpty (F : Discrete.{w} PEmpty ⥤ C) : F ≅ empty C :=
  emptyExt _ _
#align category_theory.functor.unique_from_empty CategoryTheory.Functor.uniqueFromEmpty

/-- Any two functors out of the empty category are *equal*. You probably want to use
`emptyExt` instead of this.
-/
theorem empty_ext' (F G : Discrete.{w} PEmpty ⥤ C) : F = G :=
  Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim
#align category_theory.functor.empty_ext' CategoryTheory.Functor.empty_ext'

end Functor

end CategoryTheory
