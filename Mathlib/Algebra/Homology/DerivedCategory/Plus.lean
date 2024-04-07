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
    dsimp at h
    have : (DerivedCategory.Q.obj X).IsGE n := inferInstance
    refine' ⟨n, ⟨_⟩⟩
    dsimp [t]
    change (DerivedCategory.Q.obj X).IsGE n
    infer_instance)

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
    have : IsIso (L.truncGEπ n) := by
      rw [CochainComplex.isIso_truncGEπ_iff]
      infer_instance
    refine' ⟨M, hM, (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (K.truncGEπ n),
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (CochainComplex.truncGEmap φ n ≫ inv (L.truncGEπ n)), _⟩
    erw [← (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp]
    congr 1
    rw [← cancel_mono (L.truncGEπ n), CochainComplex.truncGEπ_naturality_assoc,
      IsIso.hom_inv_id, comp_id]

variable (C)

noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Plus.ι ≅ HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh := Iso.refl _

instance : EssSurj (Qh (C := C)) := by
  suffices ∀ (X : DerivedCategory C) (n : ℤ) (_ : X.IsGE n),
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n),
      Nonempty (DerivedCategory.Q.obj K ≅ X) from ⟨by
        rintro ⟨X, n, hn⟩
        obtain ⟨K, hK, ⟨e⟩⟩ := this X n hn.mem
        refine' ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, n, hK⟩,
          ⟨Plus.ι.preimageIso e⟩⟩⟩
  intro X n hn
  have : (Q.objPreimage X).IsGE n := by
    rw [← isGE_Q_obj_iff]
    apply isGE_of_iso (Q.objObjPreimageIso X).symm
  exact ⟨(Q.objPreimage X).truncGE n, inferInstance,
    ⟨(asIso (Q.map ((Q.objPreimage X).truncGEπ n))).symm ≪≫ Q.objObjPreimageIso X⟩⟩

instance : Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).W :=
  isLocalization_of_isRightLocalizing (HomotopyCategory.Plus.ι C)
    (HomotopyCategory.subcategoryAcyclic C) (QhCompιIsoιCompQh C)

instance : Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C) := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n) (fun X => by
        refine' ⟨n, _⟩
        constructor
        change ((singleFunctor C n).obj X).IsGE n
        infer_instance))
      (fun n => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

noncomputable def homologyFunctor (n : ℤ) : Plus C ⥤ C :=
    Plus.ι ⋙ DerivedCategory.homologyFunctor C n

end Plus

end DerivedCategory
