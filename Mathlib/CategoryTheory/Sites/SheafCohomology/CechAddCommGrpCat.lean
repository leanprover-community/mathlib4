/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.EvalOpAddCommGrpCat

/-!
# Cech cohomology for presheaves of abelian groups

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type v} (U : ι → C)

section

variable {n : ℕ} (fan : ∀ (i : Fin (n + 1) → ι), Fan (U ∘ i)) (hfan : ∀ i, IsLimit (fan i))

@[simps! obj map]
def cechCochainAddCommGrpCatFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v} :=
  (FormalCoproduct.evalOpAddCommGrpCat C).flip.obj
    (op ((FormalCoproduct.mk _ U).power' fan))

noncomputable def cechComplexFunctorAddCommGrpCatObjXIso
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((cechComplexFunctor U).obj F).X n ≅
      (cechCochainAddCommGrpCatFunctor U fan).obj F :=
  ((FormalCoproduct.evalOpAddCommGrpCatIso _).app _).app _ ≪≫
    ((FormalCoproduct.evalOpAddCommGrpCat C).obj F).mapIso
      (FormalCoproduct.power'Iso (FormalCoproduct.mk _ U) fan hfan).op

end

end CategoryTheory
