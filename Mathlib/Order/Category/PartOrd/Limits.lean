/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd.Reflective
public import Mathlib.Order.Category.Preord.Limits

/-!
# Limits in `PartOrd`

`PartOrd` has all small limits as a reflective subcategory of `Preord`.
-/

public section

universe u

open CategoryTheory Limits

namespace PartOrd

instance : HasLimits PartOrd.{u} :=
  hasLimits_of_reflective (forget₂ PartOrd Preord)

end PartOrd
