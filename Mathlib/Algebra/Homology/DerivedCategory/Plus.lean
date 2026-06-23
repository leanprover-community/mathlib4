/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The bounded below derived category

Let `C` be an abelian category. In this file, we show that
the bounded below derived category `DerivedCategory.Plus C` (defined
as a full subcategory of `DerivedCategory C`) is the localization
of the bounded below homotopy category `HomotopyCategory.Plus C`
with respect to quasi-isomorphisms.

-/

@[expose] public section

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace HomotopyCategory.Plus

variable (C)

/-- The property of objects in `HomotopyCategory.Plus C` that is satisfied
by acyclic complexes. -/
abbrev subcategoryAcyclic :
    ObjectProperty (HomotopyCategory.Plus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

set_option backward.defeqAttrib.useBackward true in
lemma quasiIso_eq_subcategoryAcyclic_trW :
    HomotopyCategory.Plus.quasiIso C = (subcategoryAcyclic C).trW := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Plus.ι C).map_distinguished _ mem)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at this
  rw [dsimp% (subcategoryAcyclic C).trW_iff_of_distinguished _ mem]
  exact this

end HomotopyCategory.Plus

namespace DerivedCategory

open TStructure

variable [HasDerivedCategory C]

namespace Plus

/-- The localization functor `HomotopyCategory.Plus C ⥤ DerivedCategory.Plus C`. -/
noncomputable def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hK
    obtain ⟨n, hn⟩ := hK
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app K) n⟩)

noncomputable instance : (Qh : _ ⥤ Plus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) → _) := by
  have := CochainComplex.IsKInjective.Qh_map_bijective K.1 L.1.as
  rw [← Function.Bijective.of_comp_iff _
    ((HomotopyCategory.Plus.fullyFaithfulι C).map_bijective _ _)] at this
  rwa [← Function.Bijective.of_comp_iff' (t.plus.fullyFaithfulι.map_bijective _ _)]

instance : (HomotopyCategory.plus C).IsVerdierRightLocalizing
    (HomotopyCategory.subcategoryAcyclic C) where
  fac {K L} φ hK hL := by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hL
    obtain ⟨n, hn : L.IsStrictlyGE n⟩ := hL
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    refine ⟨(HomotopyCategory.quotient _ _).obj (K.truncGE n),
      (HomotopyCategory.quotient _ _).map (K.πTruncGE n),
      (HomotopyCategory.quotient _ _).map (CochainComplex.truncGEMap φ n ≫ inv (L.πTruncGE n)),
      ?_, ?_, by simp [← Functor.map_comp]⟩
    · simp only [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hK.truncGE _

variable (C)

/-- The functor `DerivedCategory.Plus.Qh : HomotopyCategory.Plus C ⥤ DerivedCategory.Plus C`
is induced by `DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory C`. -/
noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Plus.ι ≅ HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh := Iso.refl _

instance : (Qh (C := C)).EssSurj := by
  suffices ∀ (X : DerivedCategory C) (n : ℤ) (_ : X.IsGE n),
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n),
      Nonempty (DerivedCategory.Q.obj K ≅ X) from ⟨by
        intro ⟨X, n, K, e, h⟩
        refine ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, ?_⟩,
          ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
        · simp only [HomotopyCategory.plus_quotient_obj_iff]
          exact ⟨n, h⟩⟩
  intro X n hn
  have : (Q.objPreimage X).IsGE n := by
    rw [← isGE_Q_obj_iff]
    apply t.isGE_of_iso (Q.objObjPreimageIso X).symm
  exact ⟨(Q.objPreimage X).truncGE n, inferInstance,
    ⟨(asIso (Q.map ((Q.objPreimage X).πTruncGE n))).symm ≪≫ Q.objObjPreimageIso X⟩⟩

instance : Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).trW :=
  ((HomotopyCategory.plus C).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic C)).isLocalization_of_isLocalizedFullyFaithful
      (QhCompιIsoιCompQh C).symm

instance : Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C) := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

/-- The single functors `C ⥤ DerivedCategory.Plus C` for all `n : ℤ` along with
their compatibilities with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

/-- The single functor `C ⥤ DerivedCategory.Plus C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

/-- The single functors on `DerivedCategory.Plus C` are induced by the
single functors on `DerivedCategory C`. -/
noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ Plus.ι ≅ DerivedCategory.singleFunctor C n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

/-- The homology functor `DerivedCategory.Plus C ⥤ C` in degree `n : ℤ`. -/
noncomputable def homologyFunctor (n : ℤ) : Plus C ⥤ C :=
  Plus.ι ⋙ DerivedCategory.homologyFunctor C n
deriving Functor.IsHomological

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _
    (HomotopyCategory.Plus.subcategoryAcyclic C).trW

variable {C}

/-- The canonical t-structure on `DerivedCategory.Plus C`. -/
noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Plus C) :=
  (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

/-- Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≥ n` for the canonical t-structure. -/
abbrev IsGE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsGE X n

/-- Given `X : DerivedCategory.Plus C` and `n : ℤ`, this property means
that `X` is `≤ n` for the canonical t-structure. -/
abbrev IsLE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsLE X n

lemma isGE_ι_obj_iff (X : DerivedCategory.Plus C) (n : ℤ) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h ↦ ⟨h.1⟩

lemma isLE_ι_obj_iff (X : DerivedCategory.Plus C) (n : ℤ) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h ↦ ⟨h.1⟩

instance (X : Plus C) (n : ℤ) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance

instance (X : Plus C) (n : ℤ) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance

noncomputable instance : (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence ℤ :=
  inferInstanceAs ((ι ⋙ DerivedCategory.homologyFunctor C 0).ShiftSequence ℤ)

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  rw [← isGE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  rw [← isLE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

lemma isZero_homology_of_isGE
    (X : DerivedCategory.Plus C) (n : ℤ) [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi

lemma isZero_homology_of_isLE
    (X : DerivedCategory.Plus C) (n : ℤ) [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi

lemma isIso_iff {X Y : DerivedCategory.Plus C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  refine ⟨fun _ _ ↦ inferInstance, fun _ ↦ ?_⟩
  have : IsIso (ι.map f) := by rwa [DerivedCategory.isIso_iff]
  exact isIso_of_fully_faithful ι _

/-- The localization functor `CochainComplex.Plus C ⥤ DerivedCategory.Plus C`. -/
noncomputable def Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C :=
  HomotopyCategory.Plus.quotient C ⋙ Qh

-- TODO: show that `Q` is indeed a localization functor with respect to quasi-isomorphisms

end Plus

end DerivedCategory
