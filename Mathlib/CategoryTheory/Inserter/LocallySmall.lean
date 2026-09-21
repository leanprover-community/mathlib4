/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Inserter categories are locally small when the source category is

Given a pair of functor `F G : C ⥤ D` where `C` is locally `w`-small, we show that
`Inserter F G` is also locally `w`-small.
-/

@[expose] public section

namespace CategoryTheory.Inserter

universe w

variable {C D : Type*} [Category* C] [Category* D] [LocallySmall.{w} C]

instance (F G : C ⥤ D) : LocallySmall.{w} (Inserter F G) where
  hom_small _ _ := small_of_injective.{w} (Functor.Faithful.map_injective (F := proj F G))

end Inserter

end CategoryTheory

