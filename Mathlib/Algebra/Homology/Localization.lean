/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Composition

/-! The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQis C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we shall show that `HomologicalComplexUpToQis C c`
is also the localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms (TODO).

-/

open CategoryTheory Limits

section

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

variable {C c}

lemma isIso_Q_map_iff_mem_qis {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.qis C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.qis_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine' (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 _
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.qis C c) _ h

end HomologicalComplexUpToQis

end

section

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C] [(HomologicalComplex.qis C c).HasLocalization]

lemma HomologicalComplexUpToQis.Q_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQis.Q :=
  MorphismProperty.IsInvertedBy.of_subset _ _ _
    (Localization.inverts Q (HomologicalComplex.qis C c))
    (homotopyEquivalences_subset_qis C c)

namespace HomotopyCategory

/-- The class of quasi-isomorphisms in the homotopy category. -/
def qis : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((homologyFunctor C c i).map f)

variable {C c}

lemma mem_qis_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    qis C c f ↔ ∀ (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl

lemma quotient_map_mem_qis_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    qis C c ((quotient C c).map f) ↔ HomologicalComplex.qis C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.qis_iff, mem_qis_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

variable (C c)

lemma respectsIso_qis : (qis C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

lemma homologyFunctor_inverts_qis (i : ι) :
    (qis C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

lemma qis_eq_qis_map_quotient :
    qis C c = (HomologicalComplex.qis C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_qis_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_qis_iff] at h
    exact ((respectsIso_qis C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

/-- The condition on a complex shape `c` saying that homotopic maps become equal in
the localized category with respect to quasi-isomorphisms. -/
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.qis C c) f g

end
