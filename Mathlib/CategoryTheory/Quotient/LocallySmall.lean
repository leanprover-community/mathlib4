/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Quotient

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Quotient categories are locally small
-/

public section

universe w v u

namespace CategoryTheory.Quotient

instance {C : Type u} [Category.{v} C] (r : HomRel C) [LocallySmall.{w} C] :
    LocallySmall.{w} (Quotient r) where
  hom_small _ _ := small_of_surjective (functor r).map_surjective

end CategoryTheory.Quotient
