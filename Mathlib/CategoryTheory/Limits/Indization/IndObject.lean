import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Small
import Mathlib.Logic.Small.Set

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  (I : Type v)
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  (F : I ⥤ C)
  (ι : F ⋙ yoneda ⟶ (Functor.const I).obj A)
  (hi : IsColimit (Cocone.mk A ι))

instance {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : SmallCategory P.I :=
  P.ℐ

instance {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsFiltered P.I :=
  P.hI

def IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop :=
  Nonempty (IndObjectPresentation A)

open IsFiltered

theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) :
    IsIndObject A ↔ (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) := by
  refine' ⟨_, _⟩
  · rintro ⟨P⟩
    have := final_toCostructuredArrow_comp_pre _ P.hi
    refine' ⟨_, _⟩
    · exact IsFiltered.of_final ((Cocone.mk A P.ι).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _)
    · exact FinallySmall.mk' ((Cocone.mk A P.ι).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _)
  · rintro ⟨hI₁, hI₂⟩
    refine' ⟨_⟩
    have h₁ : (SmallFilteredIntermediate.factoring (fromFinalModel (CostructuredArrow yoneda A))
      ⋙ SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final :=
        Functor.final_of_natIso (SmallFilteredIntermediate.factoringCompInclusion _).symm
    have h₂ : Functor.Final (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
      Functor.final_of_comp_full_faithful' (SmallFilteredIntermediate.factoring _) (SmallFilteredIntermediate.inclusion _)
    let c := (tautologicalCocone A).whisker (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A)))
    let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm (isColimitTautologicalCocone A)
    have hq : _root_.Nonempty (FinalModel (CostructuredArrow yoneda A)) :=
      Nonempty.map (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
    refine' ⟨SmallFilteredIntermediate (fromFinalModel (CostructuredArrow yoneda A)),
      SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A))
        ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩

theorem IsIndObject.filtered {A : Cᵒᵖ ⥤ Type v} (h : IsIndObject A) :
    IsFiltered.{v} (CostructuredArrow yoneda A) :=
  ((isIndObject_iff _).mp h).1

theorem IsIndObject.finallySmall {A : Cᵒᵖ ⥤ Type v} (h : IsIndObject A) :
    FinallySmall.{v} (CostructuredArrow yoneda A) :=
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
    refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨i, j i y', hjs _ _, rfl⟩
    · refine ?_ ≫ (CostructuredArrow.map (colimit.ι F i)).map x
      refine CostructuredArrow.homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
      simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp]

  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)

  sorry

end CategoryTheory.Limits
