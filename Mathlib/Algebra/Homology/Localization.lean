/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Localization.HasLocalization

/-! The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQis C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain or cochain complexes),
we shall show that `HomologicalComplexUpToQis C c` is also the
localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms (TODO).

-/

open CategoryTheory Limits

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C] [(HomologicalComplex.qis C c).HasLocalization]

/-- The category of homological complexes up to quasi-isomorphisms. -/
abbrev HomologicalComplexUpToQis := (HomologicalComplex.qis C c).Localization'

variable {C c}

/-- The localization functor `HomologicalComplex C c ⥤ HomologicalComplexUpToQis C c`. -/
abbrev HomologicalComplexUpToQis.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQis C c :=
  (HomologicalComplex.qis C c).Q'

variable (C c)

lemma HomologicalComplex.homologyFunctor_inverts_qis (i : ι) :
    (qis C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
      rw [qis_iff] at hf
      dsimp
      infer_instance

namespace HomologicalComplexUpToQis

/-- The homology functor `HomologicalComplexUpToQis C c ⥤ C` for each `i : ι`. -/
noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQis C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_qis C c i) Q

/-- The homology functor on `HomologicalComplexUpToQis C c` is induced by
the homology functor on `HomologicalComplex C c`. -/
noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_qis C c i) Q

end HomologicalComplexUpToQis
