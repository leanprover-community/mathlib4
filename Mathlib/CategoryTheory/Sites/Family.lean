/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sieves
/-!

# Families of morphisms with fixed target
-/

namespace CategoryTheory

variable {C : Type*} [Category C] {X : C}

/-- A set of arrows all with codomain `X`. -/
structure Family (X : C) where
  I : Type*
  domains : I → C
  arrows : (i : I) → domains i ⟶ X

namespace Family

end Family

namespace Presieve

def toFamily (S : Presieve X) : Family X where
  I := ΣY, { f : Y ⟶ X // S f }
  domains := fun i ↦ i.fst
  arrows := fun i ↦ i.snd.val

def domains (S : Presieve X) := fun (i : ΣY, { f : Y ⟶ X // S f }) ↦ i.fst

def arrows (S : Presieve X) := fun (i : ΣY, { f : Y ⟶ X // S f }) ↦ i.snd.val

theorem arrowsPresentation (S : Presieve X) : S =
    ofArrows S.domains S.arrows := by
  funext Y f
  refine eq_iff_iff.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ofArrows.mk (⟨Y, f, h⟩ : ΣY, { f : Y ⟶ X // S f })
  · cases h with
    | mk i => exact i.snd.prop

end Presieve

end CategoryTheory
