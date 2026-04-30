/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Minus
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory

/-!
# D^-

-/

@[expose] public section

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category C] [Abelian C]

namespace HomotopyCategory

namespace Minus

variable (C)

abbrev subcategoryAcyclic :
    ObjectProperty (HomotopyCategory.Minus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Minus.ι C)

lemma quasiIso_eq_subcategoryAcyclic_trW :
    HomotopyCategory.Minus.quasiIso C = (subcategoryAcyclic C).trW := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Minus.ι C).map_distinguished _ mem)
  erw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_trW] at this
  erw [(subcategoryAcyclic C).trW_iff_of_distinguished _ mem]
  exact this

end Minus

end HomotopyCategory

namespace DerivedCategory

open TStructure

namespace Minus

variable [HasDerivedCategory C]

noncomputable def Qh : HomotopyCategory.Minus C ⥤ Minus C :=
  t.minus.lift (HomotopyCategory.Minus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨⟨X⟩, n, h⟩
    exact ⟨n, t.isLE_of_iso ((quotientCompQhIso C).symm.app X) n⟩)

noncomputable instance : (Qh : _ ⥤ Minus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (Qh : _ ⥤ Minus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

instance : (HomotopyCategory.minus C).IsTriangulatedLeftLocalizing
    (HomotopyCategory.subcategoryAcyclic C) where
  fac {K L} φ hK hL := by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨n, hn : K.IsStrictlyLE n⟩ := hK
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    refine ⟨(HomotopyCategory.quotient _ _).obj (L.truncLE n),
      (HomotopyCategory.quotient _ _).map (inv (K.ιTruncLE n) ≫ CochainComplex.truncLEMap φ n),
      (HomotopyCategory.quotient _ _).map (L.ιTruncLE n),
      ⟨n, (inferInstance : (L.truncLE n).IsStrictlyLE n)⟩, ?_, by simp [← Functor.map_comp]⟩
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact hL.truncLE _

variable (C)

noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Minus.ι ≅ HomotopyCategory.Minus.ι C ⋙ DerivedCategory.Qh := Iso.refl _

instance : (Qh (C := C)).EssSurj := by
  suffices ∀ (X : DerivedCategory C) (n : ℤ) (_ : X.IsGE n),
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n),
      Nonempty (DerivedCategory.Q.obj K ≅ X) from ⟨by
        rintro ⟨X, n, hn⟩
        obtain ⟨K, e, h⟩ := hn
        exact ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, n, h⟩,
          ⟨Minus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩⟩
  intro X n hn
  have : (Q.objPreimage X).IsGE n := by
    rw [← isGE_Q_obj_iff]
    apply t.isGE_of_iso (Q.objObjPreimageIso X).symm
  exact ⟨(Q.objPreimage X).truncGE n, inferInstance,
    ⟨(asIso (Q.map ((Q.objPreimage X).πTruncGE n))).symm ≪≫ Q.objObjPreimageIso X⟩⟩

instance : Qh.IsLocalization (HomotopyCategory.Minus.subcategoryAcyclic C).trW :=
  ObjectProperty.isLocalization_of_isTriangulated_of_isLocalizedFullyFaithful
    (QhCompιIsoιCompQh C).symm

instance : Qh.IsLocalization (HomotopyCategory.Minus.quasiIso C) := by
  rw [HomotopyCategory.Minus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

noncomputable def singleFunctors : SingleFunctors C (Minus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Minus.ι
      (fun n => t.minus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Minus C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ Minus.ι ≅ DerivedCategory.singleFunctor C n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

noncomputable def homologyFunctor (n : ℤ) : Minus C ⥤ C :=
    Minus.ι ⋙ DerivedCategory.homologyFunctor C n

instance (n : ℤ) : (homologyFunctor C n).IsHomological := by
  dsimp [homologyFunctor]
  infer_instance

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _
    (HomotopyCategory.Minus.subcategoryAcyclic C).trW

variable {C}

noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Minus C) :=
  (DerivedCategory.TStructure.t (C := C)).minus.tStructure DerivedCategory.TStructure.t

abbrev IsGE (X : Minus C) (n : ℤ) : Prop := Minus.TStructure.t.IsGE X n
abbrev IsLE (X : Minus C) (n : ℤ) : Prop := Minus.TStructure.t.IsLE X n

lemma isGE_ι_obj_iff (X : DerivedCategory.Minus C) (n : ℤ) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

lemma isLE_ι_obj_iff (X : DerivedCategory.Minus C) (n : ℤ) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

instance (X : Minus C) (n : ℤ) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance

instance (X : Minus C) (n : ℤ) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance

noncomputable instance : (DerivedCategory.Minus.homologyFunctor C 0).ShiftSequence  ℤ := by
  dsimp [homologyFunctor]
  infer_instance

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsGE n := by
  rw [← isGE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

instance (X : C) (n : ℤ) : ((singleFunctor C n).obj X).IsLE n := by
  rw [← isLE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

lemma isZero_homology_of_isGE
    (X : DerivedCategory.Minus C) (n : ℤ) [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi

lemma isZero_homology_of_isLE
    (X : DerivedCategory.Minus C) (n : ℤ) [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi

lemma isIso_iff {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro _ n
    infer_instance
  · intro h
    have : IsIso (ι.map f) := by
      rw [DerivedCategory.isIso_iff]
      exact h
    apply isIso_of_fully_faithful ι

end Minus

end DerivedCategory
