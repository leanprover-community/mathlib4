/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Functor.Dense

/-!
# Locally presentable categories and strong generators

In this file, we show that a category is locally `κ`-presentable iff
it is cocomplete and has a strong generator consisting of `κ`-presentable objects.

depends on #30168 and #29565

-/

universe w v' v u' u

namespace CategoryTheory

open Limits

instance {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [Small.{w} C] [LocallySmall.{w} D]
    {F : C ⥤ D} (X : D) : Small.{w} (CostructuredArrow F X) := by
  let φ (f : CostructuredArrow F X) : Σ (Y : C), F.obj Y ⟶ X := ⟨_, f.hom⟩
  have hφ : Function.Injective φ := by
    intro f g h
    obtain ⟨Y, f, rfl⟩ := CostructuredArrow.mk_surjective f
    obtain ⟨Z, g, rfl⟩ := CostructuredArrow.mk_surjective g
    obtain rfl : Y = Z := congr_arg Sigma.fst h
    obtain rfl : f = g := by simpa [φ] using h
    rfl
  exact small_of_injective hφ

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (κ) in
lemma HasCardinalFilteredGenerators.of_dense
    [LocallySmall.{w} C] {J : Type w} [SmallCategory.{w} J]
    (F : J ⥤ C) [F.IsDense] [∀ j, IsCardinalPresentable (F.obj j) κ]
    [∀ (X : C), IsCardinalFiltered (CostructuredArrow F X) κ] :
    HasCardinalFilteredGenerators C κ where
  exists_generators := by
    refine ⟨_, F.obj, inferInstance, fun X ↦ ?_⟩
    refine ⟨Shrink.{w} (CostructuredArrow F X), inferInstance,
      IsCardinalFiltered.of_equivalence _ (Shrink.equivalence _),
      { diag := _
        ι := _
        isColimit := (F.canonicalColimitOfIsDense X).whiskerEquivalence
          (Shrink.equivalence _).symm }, fun j ↦ ?_⟩
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective j
    exact ⟨_, ⟨(CostructuredArrow.proj _ _ ⋙ F).mapIso
      (((Shrink.equivalence _).unitIso.app f).symm)⟩⟩

lemma HasCardinalFilteredGenerators.of_small_of_dense [LocallySmall.{w} C]
    (P : ObjectProperty C) [ObjectProperty.Small.{w} P] [P.ι.IsDense]
    (hP : P ≤ isCardinalPresentable C κ)
    [∀ X, IsCardinalFiltered (CostructuredArrow P.ι X) κ] :
    HasCardinalFilteredGenerators C κ := by
  let J := ShrinkHoms (Shrink.{w} P.FullSubcategory)
  let e : P.FullSubcategory ≌ J :=
    (Shrink.equivalence P.FullSubcategory).trans (ShrinkHoms.equivalence _)
  let F := e.inverse ⋙ P.ι
  have (j : J) : IsCardinalPresentable (F.obj j) κ := hP _ (e.inverse.obj j).2
  have (X : C) : IsCardinalFiltered (CostructuredArrow F X) κ :=
    IsCardinalFiltered.of_equivalence _
      (CostructuredArrow.pre e.inverse P.ι X).asEquivalence.symm
  exact HasCardinalFilteredGenerators.of_dense κ F

lemma HasCardinalFilteredGenerators.of_essentiallySmall_of_dense [LocallySmall.{w} C]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P]
    [P.IsClosedUnderIsomorphisms] [P.ι.IsDense]
    [∀ X, IsCardinalFiltered (CostructuredArrow P.ι X) κ]
    (hP : P ≤ isCardinalPresentable C κ) :
    HasCardinalFilteredGenerators C κ := by
    have := ObjectProperty.EssentiallySmall.exists_small.{w} P
    obtain ⟨P₀, _, rfl⟩ := ObjectProperty.EssentiallySmall.exists_small.{w} P
    let e : P₀.FullSubcategory ≌ P₀.isoClosure.FullSubcategory :=
      (ObjectProperty.ιOfLE P₀.le_isoClosure).asEquivalence
    have : P₀.ι.IsDense := inferInstanceAs (e.functor ⋙ P₀.isoClosure.ι).IsDense
    have (X : C) : IsCardinalFiltered (CostructuredArrow P₀.ι X) κ :=
      IsCardinalFiltered.of_equivalence _
        ((CostructuredArrow.pre e.functor P₀.isoClosure.ι X).asEquivalence).symm
    exact HasCardinalFilteredGenerators.of_small_of_dense P₀
      (by rwa [← ObjectProperty.isoClosure_le_iff])

namespace IsCardinalLocallyPresentable

variable (C κ) in
lemma iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (S : Set C) (_ : Small.{w} S), IsStrongGenerator S ∧
        ∀ (X : S), IsCardinalPresentable X.1 κ := by
  refine ⟨fun _ ↦ ?_, fun ⟨S, _, hS₁, hS₂⟩ ↦ ?_⟩
  · obtain ⟨ι, G, hG⟩ := HasCardinalFilteredGenerators.exists_generators C κ
    refine ⟨Set.range G, inferInstance, hG.isStrongGenerator, ?_⟩
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hG.isCardinalPresentable i
  · let P : ObjectProperty C := S
    have : ObjectProperty.Small.{w} P := by assumption
    have (X : C) : IsCardinalFiltered
      (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) κ := ⟨fun {J} _ K hJ ↦ ⟨by
        have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
        exact colimit.cocone K⟩⟩
    have : (P.colimitsCardinalClosure κ).ι.IsDense := sorry
    have := HasCardinalFilteredGenerators.of_essentiallySmall_of_dense
      (P.colimitsCardinalClosure κ) (P.colimitsCardinalClosure_le κ
        (fun J _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C κ hJ)
        (fun X hX ↦ hS₂ ⟨X, hX⟩))
    constructor

end IsCardinalLocallyPresentable

end CategoryTheory
