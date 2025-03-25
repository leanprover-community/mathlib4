/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Robin Carlier
-/

import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Fully fathful functors respect isomorphisms.

This file records the fact that fully faithful functors reflect
isomorphisms. It has been splitted away from
`CategoryTheory.Functor.ReflectsIso.Basic` to reduce imports.

-/

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category C]
  {D : Type*} [Category D]

lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D} (hF : F.FullyFaithful) :
    F.ReflectsIsomorphisms where
  reflects _ _ := hF.isIso_of_isIso_map _

instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful] :
    F.ReflectsIsomorphisms :=
  (Functor.FullyFaithful.ofFullyFaithful F).reflectsIsomorphisms

end CategoryTheory
