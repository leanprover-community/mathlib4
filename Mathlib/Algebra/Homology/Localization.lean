/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Composition

/-! The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQis C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we show that `HomologicalComplexUpToQis C c` is also the
localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms.

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

/-- The condition on a complex shape `c` saying that homotopic maps become equal in
the localized category with respect to quasi-isomorphisms. -/
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.qis C c) f g

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

namespace HomologicalComplexUpToQis

variable {C c}
variable [c.QFactorsThroughHomotopy C]

lemma Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g :=
  (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

/-- The functor `HomotopyCategory C c ⥤ HomologicalComplexUpToQis C c` from the homotopy
category to the localized category with respect to quasi-isomorphisms. -/
def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQis C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQis.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

variable (C c)

/-- The canonical isomorphism `HomotopyCategory.quotient C c ⋙ Qh ≅ Q`. -/
def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift

lemma Qh_inverts_qis : (HomotopyCategory.qis C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_qis_iff φ,
    ← HomologicalComplexUpToQis.isIso_Q_map_iff_mem_qis]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

instance : (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization (HomologicalComplex.qis C c) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

/-- The homology functor on `HomologicalComplexUpToQis C c` is induced by
the homology functor on `HomotopyCategory C c`. -/
noncomputable def homologyFunctorFactorsh (i : ι ) :
    Qh ⋙ homologyFunctor C c i ≅ HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i  ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

section

variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]

/-- The category `HomologicalComplexUpToQis C c` which was defined as a localization of
`HomologicalComplex C c` with respect to quasi-isomorphisms also identify to a localization
of the homotopy category with respect ot quasi-isomorphisms. -/
instance : HomologicalComplexUpToQis.Qh.IsLocalization (HomotopyCategory.qis C c) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.qis C c) (HomologicalComplex.qis C c)
    (homotopyEquivalences_subset_qis C c)
    (HomotopyCategory.qis_eq_qis_map_quotient C c)

end

end HomologicalComplexUpToQis

end

section Cylinder

variable {ι : Type*} (c : ComplexShape ι) (hc : ∀ j, ∃ i, c.Rel i j)
  (C : Type*) [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The homotopy category satisfies the universal property of the localized category
with respect to homotopy equivalences. -/
def ComplexShape.strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quotient C c)
      (HomologicalComplex.homotopyEquivalences C c) E where
  inverts := HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac F hF := rfl
  uniq F₁ F₂ h := Quotient.lift_unique' _ _ _ h

lemma ComplexShape.quotient_isLocalization :
    (HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) := by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc

lemma ComplexShape.QFactorsThroughHomotopy_of_exists_prev [CategoryWithHomology C] :
    c.QFactorsThroughHomotopy C where
  areEqualizedByLocalization {K L f g} h := by
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_subset _ _ _
        (Localization.inverts _ (HomologicalComplex.qis C _))
        (homotopyEquivalences_subset_qis C _))

end Cylinder

section ChainComplex

variable (C : Type*) [Category C] {ι : Type*} [Preadditive C]
  [AddRightCancelSemigroup ι] [One ι] [HasBinaryBiproducts C]

instance : (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C

variable [CategoryWithHomology C]

instance : (ComplexShape.down ι).QFactorsThroughHomotopy C :=
  (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C

example [(HomologicalComplex.qis C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQis.Qh.IsLocalization (HomotopyCategory.qis C (ComplexShape.down ι)) :=
  inferInstance

/- By duality, the results obtained here for chain complexes could be dualized in
order to obtain similar results for general cochain complexes. However, the case of
interest for the construction of the derived category (cochain complexes indexed by `ℤ`)
can also be obtained directly, which is done below. -/

end ChainComplex

section CochainComplex

variable (C : Type*) [Category C] {ι : Type*} [Preadditive C] [HasBinaryBiproducts C]

instance : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.up ℤ).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C

variable [CategoryWithHomology C]

instance : (ComplexShape.up ℤ).QFactorsThroughHomotopy C :=
  (ComplexShape.up ℤ).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C

/-- When we define the derived category as `HomologicalComplexUpToQis C (ComplexShape.up ℤ)`,
i.e. as the localization of cochain complexes with respect to quasi-isomorphisms, this
example shall say that the derived category is also the localization of the homotopy
category with respect to quasi-isomorphisms. -/
example [(HomologicalComplex.qis C (ComplexShape.up ℤ)).HasLocalization] :
    HomologicalComplexUpToQis.Qh.IsLocalization (HomotopyCategory.qis C (ComplexShape.up ℤ)) :=
  inferInstance

end CochainComplex
