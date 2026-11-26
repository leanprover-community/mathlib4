/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

import Mathlib.CategoryTheory.Functor.RegularEpi

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# The category of simplicial sets is a regular epi category
-/

public section

universe u

open CategoryTheory

namespace SSet

instance : IsRegularEpiCategory SSet.{u} :=
  inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

end SSet
