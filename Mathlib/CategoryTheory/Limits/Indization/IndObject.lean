/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Small
import Mathlib.Logic.Small.Set

/-!
# Ind-objects

For a presheaf `A : Cᵒᵖ ⥤ Type v` we define the type `IndObjectPresentation A` of presentations
of `A` as small filtered colimits of representable presheaves and define the predicate
`IsIndObject A` asserting that there is at least one such presentation.

## Future work

A presheaf is an ind-object if and only if the category `CostructuredArrow yoneda A` is filtered
and finally small. In this way, `CostructuredArrow yoneda A` can be thought of the universal
indexing category for the representation of `A` as a small filtered colimit of representable
presheaves.

There are various useful ways to understand natural transformations between ind-objects in terms
of their presentations.

The ind-objects form a locally `v`-small category `IndCategory C` which has numerous interesting
properties.

## Implementation notes

One might be tempted to introduce another universe parameter and consider being a `w`-ind-object
as a property of presheaves `C ⥤ TypeMax.{v, w}`. This comes with significant technical hurdles.
The recommended alternative is to consider ind-objects over `ULiftHom.{w} C` instead.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The data that witnesses that a presheaf `A` is an ind-object. It consists of a small
    filtered indexing category `I`, a diagram `F : I ⥤ C` and the data for a colimit cocone on
    `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v` with cocone point `A`. -/
structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  (I : Type v)
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  (F : I ⥤ C)
  (ι : F ⋙ yoneda ⟶ (Functor.const I).obj A)
  (isColimit : IsColimit (Cocone.mk A ι))

namespace IndObjectPresentation

variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)

instance : SmallCategory P.I := P.ℐ
instance : IsFiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps]
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι

/-- `P.cocone` is a colimit cocone. -/
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit

/-- The canonical comparison functor between the indexing category of the presentation and the
    comma category `CostructuredArrow yoneda A`. This functor is always final. -/
@[simps!]
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

instance : P.toCostructuredArrow.Final :=
  final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

/-- Representable presheaves are (trivially) ind-objects. -/
@[simps]
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun s => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun s m h => h ⟨PUnit.unit⟩ }

end IndObjectPresentation

/-- A presheaf is called an ind-object if it can be written as a filtered colimit of representable
    presheaves. -/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)

theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩

/-- Representable presheaves are (trivially) ind-objects. -/
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
  .mk <| IndObjectPresentation.yoneda X

open IsFiltered

theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) :
    IsIndObject A ↔ (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) := by
  refine ⟨fun ⟨⟨P⟩⟩ => ?_, ?_⟩
  · exact ⟨IsFiltered.of_final P.toCostructuredArrow, FinallySmall.mk' P.toCostructuredArrow⟩
  · rintro ⟨hI₁, hI₂⟩
    have h₁ : (SmallFilteredIntermediate.factoring (fromFinalModel (CostructuredArrow yoneda A))
      ⋙ SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final :=
        Functor.final_of_natIso (SmallFilteredIntermediate.factoringCompInclusion _).symm
    have h₂ : Functor.Final (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
      Functor.final_of_comp_full_faithful' (SmallFilteredIntermediate.factoring _) (SmallFilteredIntermediate.inclusion _)
    let c := (tautologicalCocone A).whisker (SmallFilteredIntermediate.inclusion (fromFinalModel (CostructuredArrow yoneda A)))
    let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm (isColimitTautologicalCocone A)
    have hq : _root_.Nonempty (FinalModel (CostructuredArrow yoneda A)) :=
      Nonempty.map (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
    exact ⟨SmallFilteredIntermediate (fromFinalModel (CostructuredArrow yoneda A)),
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
