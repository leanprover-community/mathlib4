import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Filtered.Small

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

structure IndObjectPresentation (X : Cᵒᵖ ⥤ Type v) where
  (I : Type v)
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  (F : I ⥤ C)
  (ι : F ⋙ yoneda ⟶ (Functor.const I).obj X)
  (hi : IsColimit (Cocone.mk X ι))

instance {X : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation X) : SmallCategory P.I :=
  P.ℐ

instance {X : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation X) : IsFiltered P.I :=
  P.hI

def IsIndObject (X : Cᵒᵖ ⥤ Type v) : Prop :=
  Nonempty (IndObjectPresentation X)

open IsFiltered

theorem IsIndObject_iff (X : Cᵒᵖ ⥤ Type v) :
    IsIndObject X ↔ (IsFiltered (CostructuredArrow yoneda X) ∧ FinallySmall.{v} (CostructuredArrow yoneda X)) := by
  refine' ⟨_, _⟩
  · rintro ⟨P⟩
    have := final_toCostructuredArrow_comp_pre _ P.hi
    refine' ⟨_, _⟩
    · exact IsFiltered.of_final ((Cocone.mk X P.ι).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _)
    · exact FinallySmall.mk' ((Cocone.mk X P.ι).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _)
  · rintro ⟨hI₁, hI₂⟩
    refine' ⟨_⟩
    have h₁ : (SmallFilteredIntermediate.factoring (fromFinalModel (CostructuredArrow yoneda X))
      ⋙ SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda X))).Final :=
        Functor.final_of_natIso (SmallFilteredIntermediate.factoringCompInclusion _).symm
    have h₂ : Functor.Final (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda X))) :=
      Functor.final_of_comp_full_faithful' (SmallFilteredIntermediate.factoring _) (SmallFilteredIntermediate.inclusion _)
    let c := (tautologicalCocone X).whisker (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda X)))
    let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm (isColimitTautologicalCocone X)
    have hq : _root_.Nonempty (FinalModel (CostructuredArrow yoneda X)) :=
      Nonempty.map (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda X))) IsFiltered.nonempty
    refine' ⟨SmallFilteredIntermediate (fromFinalModel (CostructuredArrow yoneda X)),
      SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda X))
        ⋙ CostructuredArrow.proj yoneda X, c.ι, hc⟩

end CategoryTheory.Limits
