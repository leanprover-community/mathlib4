/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The category of presheaves of modules over a scheme

In this file, given a scheme `X`, we define the category of presheaves
of modules over `X`. As categories of presheaves of modules are
defined for presheaves of rings (and not presheaves of commutative rings),
we also introduce a definition `X.ringCatSheaf` for the underlying sheaf
of rings of `X`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The underlying sheaf of rings of a scheme. -/
abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of presheaves of modules over a scheme. -/
nonrec abbrev PresheafOfModules := PresheafOfModules.{u} X.ringCatSheaf.val

end AlgebraicGeometry.Scheme
