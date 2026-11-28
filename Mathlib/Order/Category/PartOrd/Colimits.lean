/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd.Reflective
public import Mathlib.Order.Category.Preord.Colimits

/-!
# Colimits in `PartOrd`

`PartOrd` has all small colimits as a reflective subcategory of `Preord`.
-/

public section

universe u

open CategoryTheory Limits

namespace PartOrd

instance : HasColimits PartOrd.{u} :=
  hasColimits_of_reflective (forget₂ PartOrd Preord)

end PartOrd
