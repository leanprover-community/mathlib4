/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The opposite of a subcomplex

-/

@[expose] public section

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The opposite of subcomplex, as a subcomplex of the opposite simplicial set. -/
protected def op : X.op.Subcomplex where
  obj := A.obj
  map _ := A.map _

lemma mem_op_obj_iff {d : SimplexCategoryᵒᵖ} (x : X.op.obj d) :
    x ∈ A.op.obj d ↔ X.opObjEquiv x ∈ A.obj d := Iff.rfl

end SSet.Subcomplex
