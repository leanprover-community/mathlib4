/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Predicate

/-! Morphism properties equipped with a localized category

If `C : Type u` is a category (with `[Category.{v} C]`), and
`W : MorphismProperty C`, then the constructed localized
category `W.Localization` is in `Type u` (the objects are
essentially the same as that of `C`), but the morphisms
are in `Type (max u v)`. In particular situations, it
may happen that there is a localized category for `W`
whose morphisms are in a lower universe like `v`: it shall
be so for the homotopy categories of model categories (TODO),
and it should also be so for the derived categories of
Grothendieck abelian categories (TODO: but this shall be
very technical).

Then, in order to allow the user to provide a localized
category with specific universe parameters when it exists,
we introduce a typeclass `MorphismProperty.HasLocalization.{w} W`
which contains the data of a localized category `D` for `W`
with `D : Type u` and `[Category.{w} D]`. Then, all
definitions which involve "the" localized category
for `W` should contain a `[MorphismProperty.HasLocalization.{w} W]`
assumption for a suitable `w`. The functor `W.Q' : C ⥤ W.Localization'`
shall be the localization functor for this fixed choice of the
localized category. If the statement of a theorem does not
involve the localized category, but the proof does,
it is no longer necessary to use a `HasLocalization`
assumption, but one may use
`HasLocalization.standard` in the proof instead.

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

namespace MorphismProperty

/-- The data of a localized category with a given universe
for the morphisms.  -/
class HasLocalization where
  /-- the objects of the localized category. -/
  {D : Type u}
  /-- the category structure. -/
  [hD : Category.{w} D]
  /-- the localization functor. -/
  L : C ⥤ D
  [hL : L.IsLocalization W]

variable [HasLocalization.{w} W]

/-- The localized category for `W : MorphismProperty C`
that is fixed by the `[HasLocalization W]` instance. -/
def Localization' := HasLocalization.D W

instance : Category W.Localization' := HasLocalization.hD

/-- The localization functor `C ⥤ W.Localization'`
that is fixed by the `[HasLocalization W]` instance. -/
def Q' : C ⥤ W.Localization' := HasLocalization.L

instance : W.Q'.IsLocalization W := HasLocalization.hL

/-- The constructed localized category. -/
def HasLocalization.standard : HasLocalization.{max u v} W where
  L := W.Q

end MorphismProperty

end CategoryTheory
