/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# The range of a dense functor if a strong generator

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

open ObjectProperty in
lemma isStrongGenerator_of_isDense (F : C ⥤ D) [F.IsDense] :
    IsStrongGenerator (.ofObj F.obj) :=
  (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y ↦ ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩⟩))

end CategoryTheory.Functor
