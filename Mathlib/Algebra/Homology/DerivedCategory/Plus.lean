import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Shift.SingleFunctorsLift
import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace HomotopyCategory

namespace Plus

variable (C)

abbrev subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory.Plus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

lemma quasiIso_eq_subcategoryAcyclic_W :
    HomotopyCategory.Plus.quasiIso C = (subcategoryAcyclic C).W := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have mem' := (HomotopyCategory.Plus.ι C).map_distinguished _ mem
  erw [(subcategoryAcyclic C).mem_W_iff_of_distinguished _ mem,
    ← (HomotopyCategory.subcategoryAcyclic C).mem_W_iff_of_distinguished _ mem',
    ← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  rfl

end Plus

end HomotopyCategory

namespace DerivedCategory

open TStructure

namespace Plus

def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨⟨X⟩, n, h⟩
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app X) n⟩)

noncomputable instance : (Qh : _ ⥤ Plus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) → _) :=
  CochainComplex.Qh_map_bijective_of_isKInjective K.1 L.1.as

instance : IsRightLocalizing (HomotopyCategory.Plus.ι C)
    (HomotopyCategory.subcategoryAcyclic C) where
  fac {K L} φ hK := by
    obtain ⟨K : CochainComplex C ℤ⟩ := K
    obtain ⟨⟨L : CochainComplex C ℤ⟩, n, (hn : L.IsStrictlyGE n)⟩ := L
    obtain ⟨φ, rfl⟩ : ∃ (ψ : K ⟶ L), φ = (HomotopyCategory.quotient _ _).map ψ := by
      obtain ⟨ψ⟩ := φ
      exact ⟨ψ, rfl⟩
    let M : HomotopyCategory.Plus C :=
      ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (K.truncGE n), n, by
        change (K.truncGE n).IsStrictlyGE n
        infer_instance⟩
    have hM : (HomotopyCategory.subcategoryAcyclic C).P ((HomotopyCategory.Plus.ι C).obj M) := by
      dsimp [M, HomotopyCategory.Plus.ι, Subcategory.ι]
      rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
        K.acyclic_truncGE_iff (n - 1) n (by omega)]
      erw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
      exact ⟨fun i _ => by simpa only [HomologicalComplex.exactAt_iff_isZero_homology] using hK i⟩
    have : IsIso (L.πTruncGE n) := by
      rw [CochainComplex.isIso_πTruncGE_iff]
      infer_instance
    refine' ⟨M, hM, (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (K.πTruncGE n),
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (CochainComplex.truncGEMap φ n ≫ inv (L.πTruncGE n)), _⟩
    erw [← (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp]
    congr 1
    rw [← cancel_mono (L.πTruncGE n), CochainComplex.πTruncGE_naturality_assoc,
      IsIso.hom_inv_id, comp_id]

variable (C)

noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Plus.ι ≅ HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh := Iso.refl _

instance : (Qh (C := C)).EssSurj := by
  suffices ∀ (X : DerivedCategory C) (n : ℤ) (_ : X.IsGE n),
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n),
      Nonempty (DerivedCategory.Q.obj K ≅ X) from ⟨by
        rintro ⟨X, n, hn⟩
        obtain ⟨K, e, h⟩ := hn.mem
        refine' ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, n, h⟩,
          ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩⟩
  intro X n hn
  have : (Q.objPreimage X).IsGE n := by
    rw [← isGE_Q_obj_iff]
    apply t.isGE_of_iso (Q.objObjPreimageIso X).symm
  exact ⟨(Q.objPreimage X).truncGE n, inferInstance,
    ⟨(asIso (Q.map ((Q.objPreimage X).πTruncGE n))).symm ≪≫ Q.objObjPreimageIso X⟩⟩

instance : Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).W :=
  isLocalization_of_isRightLocalizing (HomotopyCategory.Plus.ι C)
    (HomotopyCategory.subcategoryAcyclic C) (QhCompιIsoιCompQh C)

instance : Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C) := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ Plus.ι ≅ DerivedCategory.singleFunctor C n := by
  apply SingleFunctors.liftFunctorCompIso

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

noncomputable def homologyFunctor (n : ℤ) : Plus C ⥤ C :=
    Plus.ι ⋙ DerivedCategory.homologyFunctor C n

instance (n : ℤ) : (homologyFunctor C n).IsHomological := by
  dsimp [homologyFunctor]
  infer_instance

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow_of_hasLeftCalculusofFractions _
    (HomotopyCategory.Plus.subcategoryAcyclic C).W

variable {C}

abbrev TStructure.t : TStructure (DerivedCategory.Plus C) :=
  (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

abbrev IsGE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsGE X n
abbrev IsLE (X : Plus C) (n : ℤ) : Prop := Plus.TStructure.t.IsLE X n

lemma isGE_ι_obj_iff (X : DerivedCategory.Plus C) (n : ℤ) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

lemma isLE_ι_obj_iff (X : DerivedCategory.Plus C) (n : ℤ) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

instance (X : Plus C) (n : ℤ) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance

instance (X : Plus C) (n : ℤ) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance

noncomputable instance : (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence  ℤ := by
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
    (X : DerivedCategory.Plus C) (n : ℤ) [X.IsGE n] (i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi

lemma isZero_homology_of_isLE
    (X : DerivedCategory.Plus C) (n : ℤ) [X.IsLE n] (i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi

lemma isIso_iff {X Y : DerivedCategory.Plus C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro _ n
    infer_instance
  · intro h
    have : IsIso (ι.map f) := by
      rw [DerivedCategory.isIso_iff]
      exact h
    apply isIso_of_fully_faithful ι

end Plus

end DerivedCategory
