/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.Order.Category.Preord.Reflective

/-!
# Colimits in `Preord`

`Preord` has all small colimits as a reflective subcategory of `Cat`.
-/

public section

universe u

open CategoryTheory Limits

namespace Preord

instance : HasColimits Preord.{u} :=
  hasColimits_of_reflective preordToCat

end Preord
