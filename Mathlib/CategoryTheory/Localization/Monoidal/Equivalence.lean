/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Comparing a monoidal localization with an existing monoidal structure
-/

@[expose] public section

open CategoryTheory Localization.Monoidal MonoidalCategory

noncomputable section

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

variable [MonoidalCategory D]

namespace CategoryTheory.Localization.Monoidal

/-- A monoidal category is equivalent to its transported localized monoidal structure. -/
@[simps!]
def equivLocalizedMonoidal : D ≌ LocalizedMonoidal L W ε := CategoryTheory.Equivalence.refl

open Functor.Monoidal Functor.LaxMonoidal Functor.OplaxMonoidal

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).inverse.Monoidal :=
  letI : (L' ⋙ (equivLocalizedMonoidal L W ε).inverse).Monoidal := inferInstanceAs L.Monoidal
  letI : Localization.Lifting L W (L' ⋙ (equivLocalizedMonoidal L W ε).inverse)
    (equivLocalizedMonoidal L W ε).inverse  := ⟨Iso.refl _⟩
  functorMonoidalOfComp L' W (equivLocalizedMonoidal L W ε).inverse
    (L' ⋙ (equivLocalizedMonoidal L W ε).inverse)

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).functor.Monoidal :=
  (equivLocalizedMonoidal L W ε).symm.inverseMonoidal

end CategoryTheory.Localization.Monoidal
