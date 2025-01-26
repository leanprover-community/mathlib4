/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subpresheaf.Basic
import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Comparison of `Subpresheaf` and `MonoOver`
-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)

namespace Subpresheaf

def toMonoOverEquivalence : Subpresheaf F ≌ MonoOver F where
  functor :=
    { obj A := MonoOver.mk' A.ι
      map {A B} f := MonoOver.homMk (Subpresheaf.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := by
        have pif := X.obj.hom
        have pif := Subpresheaf.range
        dsimp at pif
        sorry
      map := sorry
      map_id := sorry
      map_comp := sorry }
  unitIso := sorry
  counitIso := sorry

end Subpresheaf

end CategoryTheory
