/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal

/-!
# The nerve of a category is a quasicategory

This file defines a `Quasicategory` instance for the nerve of a category. This
is a direct consequence of the proofs in
`AlgebraicTopology.Quasicategory.StrictSegal` that the nerve of a category is
`StrictSegal` and that any `StrictSegal` simplicial set is a quasicategory.
-/

universe v u

open CategoryTheory SSet

namespace Nerve

/-- By virtue of satisfying the `StrictSegal` condition, the nerve of a
category is a `Quasicategory`. -/
instance quasicategory {C : Type u} [Category.{v} C] :
  Quasicategory (nerve C) := inferInstance

end Nerve
