import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Small
import Mathlib.Logic.Small.Set

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

theorem isIndObject_iff (X : Cᵒᵖ ⥤ Type v) :
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

theorem IsIndObject.finallySmall {X : Cᵒᵖ ⥤ Type v} (h : IsIndObject X) :
    FinallySmall.{v} (CostructuredArrow yoneda X) :=
  ((isIndObject_iff _).mp h).2

theorem presheaf_colim_jointly_surjective (I : Type v) [SmallCategory I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) (x : (colimit F).obj X) :
    ∃ j y, x = (colimit.ι F j).app X y := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective'.{v, v} ((colimitObjIsoColimitCompEvaluation F X).hom x)
  refine' ⟨j, y, ?_⟩
  apply (colimitObjIsoColimitCompEvaluation F X).toEquiv.injective
  simp [← hy, elementwise_of% colimitObjIsoColimitCompEvaluation_ι_app_hom F]
  rfl -- wat?

theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFilteredOrEmpty I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  suffices IsFiltered (CostructuredArrow yoneda (colimit F)) by
    refine (isIndObject_iff _).mpr ⟨this, ?_⟩
    have : ∀ i, ∃ (s : Set (CostructuredArrow yoneda (F.obj i)))
      (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := fun i =>
        (hF i).finallySmall.exists_small_weakly_terminal_set
    choose s hs j hjs hj using this
    have : Small.{v} (⋃ i, (CostructuredArrow.map (colimit.ι F i)).obj '' (s i)) := small_iUnion _
    refine finallySmall_of_small_weakly_terminal_set
      (⋃ i, (CostructuredArrow.map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
    obtain ⟨i, y, hy⟩ := presheaf_colim_jointly_surjective I F _ (yonedaEquiv A.hom)
    let y' : CostructuredArrow yoneda (F.obj i) := CostructuredArrow.mk (yonedaEquiv.symm y)
    obtain ⟨x⟩ := hj _ y'
    refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj (j i y'), ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨i, j i y', hjs _ _, rfl⟩
    · refine ⟨CostructuredArrow.homMk x.left ?_⟩
      apply yonedaEquiv.injective
      dsimp only [Functor.const_obj_obj, CostructuredArrow.map_obj_left,
        CostructuredArrow.map_obj_right, CostructuredArrow.map_obj_hom]
      rw [hy]
      simp [yonedaEquiv_apply]

  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} F => ?_)

  sorry

end CategoryTheory.Limits
