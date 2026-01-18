/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Quotient group-seminorms and related constructions
-/

@[expose] public section

open Function Set

namespace GroupSeminorm

variable {E F : Type*} [Group E] [Group F]

@[to_additive]
noncomputable def map (p : GroupSeminorm E) (f : E →* F) : GroupSeminorm F where
  toFun x := open scoped Classical in
    if Surjective f
    then sInf (p '' (f ⁻¹' {x}))
    else 0
  map_one' := by
    split_ifs
    · exact IsLeast.csInf_eq ⟨⟨1, map_one f, map_one_eq_zero p⟩,
        forall_mem_image.mpr fun _ _ ↦ apply_nonneg _ _⟩
    · rfl
  mul_le' x y := by
    split_ifs
    · rw [← csInf_add]
    · simp
  inv' x := sorry


end GroupSeminorm

end
