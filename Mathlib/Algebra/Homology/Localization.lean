/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Localization.HasLocalization

/-! The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQuasiIso C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we shall show that `HomologicalComplexUpToQuasiIso C c`
is also the localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms (TODO).

-/

open CategoryTheory Limits

section

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C] [(HomologicalComplex.quasiIso C c).HasLocalization]

/-- The category of homological complexes up to quasi-isomorphisms. -/
abbrev HomologicalComplexUpToQuasiIso := (HomologicalComplex.quasiIso C c).Localization'

variable {C c}

/-- The localization functor `HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c`. -/
abbrev HomologicalComplexUpToQuasiIso.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  (HomologicalComplex.quasiIso C c).Q'

variable (C c)

lemma HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
      rw [mem_quasiIso_iff] at hf
      dsimp
      infer_instance

namespace HomologicalComplexUpToQuasiIso

/-- The homology functor `HomologicalComplexUpToQuasiIso C c ⥤ C` for each `i : ι`. -/
noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

/-- The homology functor on `HomologicalComplexUpToQuasiIso C c` is induced by
the homology functor on `HomologicalComplex C c`. -/
noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

variable {C c}

lemma isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine' (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 _
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

end HomologicalComplexUpToQuasiIso

end

section

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C] [(HomologicalComplex.quasiIso C c).HasLocalization]

lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q :=
  MorphismProperty.IsInvertedBy.of_subset _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_subset_quasiIso C c)

namespace HomotopyCategory

/-- The class of quasi-isomorphisms in the homotopy category. -/
def quasiIso : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((homologyFunctor C c i).map f)

variable {C c}

lemma mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    quasiIso C c f ↔ ∀ (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl

lemma quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

variable (C c)

lemma respectsIso_quasiIso : (quasiIso C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

lemma homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

lemma quasiIso_eq_quasiIso_map_quotient :
    quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((respectsIso_quasiIso C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

/-- The condition on a complex shape `c` saying that homotopic maps become equal in
the localized category with respect to quasi-isomorphisms. -/
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g

end
