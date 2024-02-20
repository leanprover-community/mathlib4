/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.DiscreteCategory

#align_import category_theory.pempty from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

/-!
# The empty category

Defines a category structure on `PEmpty`, and the unique functor `PEmpty ⥤ C` for any category `C`.
-/

universe w v v' u u'
-- morphism levels before object levels. See note [CategoryTheory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]

instance (α : Type*) [IsEmpty α] : IsEmpty (Discrete α) := Function.isEmpty Discrete.as

/-- The (unique) functor from an empty category. -/
def functorOfIsEmpty [IsEmpty C] : C ⥤ D where
  obj := isEmptyElim
  map := fun {X} ↦ isEmptyElim X
  map_id := fun {X} ↦ isEmptyElim X
  map_comp := fun {X} ↦ isEmptyElim X

variable {C D}

/-- Any two functors out of an empty category are isomorphic. -/
def Functor.isEmptyExt [IsEmpty C] (F G : C ⥤ D) : F ≅ G :=
  NatIso.ofComponents isEmptyElim (fun {X} ↦ isEmptyElim X)

variable (C D)

/-- The equivalence between two empty categories. -/
def equivalenceOfIsEmpty [IsEmpty C] [IsEmpty D] : C ≌ D where
  functor := functorOfIsEmpty C D
  inverse := functorOfIsEmpty D C
  unitIso := Functor.isEmptyExt _ _
  counitIso := Functor.isEmptyExt _ _
  functor_unitIso_comp := isEmptyElim

/-- Equivalence between two empty categories. -/
def emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty := equivalenceOfIsEmpty _ _
#align category_theory.functor.empty_equivalence CategoryTheory.emptyEquivalence

namespace Functor

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
