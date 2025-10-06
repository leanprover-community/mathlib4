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
This is theorem 1.20 in the book by Adámek and Rosický.

In particular, if a category if locally `κ`-presentable, if it also
locally `κ'`-presentable for any regular cardinal `κ'` such that `κ ≤ κ'`.

We also show that in a locally presentable category,
the `κ`-presentable objects form an essentially small category
for any regular cardinal `κ`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v' v u' u

namespace CategoryTheory

-- to be moved
instance CostructuredArrow.locallySmall {C : Type u} {D : Type u'} [Category.{u'} C]
    [Category.{v'} D] (F : C ⥤ D) (Y : D) [LocallySmall.{w} C] :
    LocallySmall.{w} (CostructuredArrow F Y) where
  hom_small T₁ T₂ := small_of_injective (f := CommaMorphism.left)
    (fun _ _ _ ↦ by aesop)

-- to be moved
instance CostructuredArrow.small {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
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

-- to be moved
instance CostructuredArrow.essentiallySmall {C : Type u} {D : Type u'} [Category.{v} C]
    [Category.{v'} D] (F : C ⥤ D) (Y : D) [EssentiallySmall.{w} C] [LocallySmall.{w} D] :
    EssentiallySmall.{w} (CostructuredArrow F Y) := by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse F Y).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

open Limits

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

instance ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsCardinalFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) κ where
  nonempty_cocone {J} _ K hJ := ⟨by
    have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
    exact colimit.cocone K⟩

instance ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) :=
  isFiltered_of_isCardinalDirected _ κ

lemma IsStrongGenerator.isDense_colimitsCardinalClosure_ι
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : IsStrongGenerator P)
    (hS₂ : P ≤ isCardinalPresentable C κ) :
    (P.colimitsCardinalClosure κ).ι.IsDense where
  isCanonicalColimit_eq_top := by
    ext X
    simp only [Pi.top_apply, «Prop».top_eq_true, iff_true]
    have : HasColimitsOfShape (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) C := by
      obtain ⟨P₀, _, hP₀⟩ :=
        ObjectProperty.EssentiallySmall.exists_small.{w} (P.colimitsCardinalClosure κ)
      have h : P₀ ≤ P.colimitsCardinalClosure κ := by simp only [hP₀, P₀.le_isoClosure]
      have : (ObjectProperty.ιOfLE h).IsEquivalence :=
        (ObjectProperty.isEquivalence_ιOfLE_iff h).2 (by rw [hP₀])
      let e : P₀.FullSubcategory ≌ (P.colimitsCardinalClosure κ).FullSubcategory :=
        (ObjectProperty.ιOfLE h).asEquivalence
      have : HasColimitsOfShape
          (CostructuredArrow (e.functor ⋙ (P.colimitsCardinalClosure κ).ι) X) C :=
        HasColimitsOfShape.of_essentiallySmall.{w} _ _
      apply hasColimitsOfShape_of_equivalence
        (CostructuredArrow.pre e.functor (ObjectProperty.ι _) X).asEquivalence
    let c := canonicalCocone (P.colimitsCardinalClosure κ).ι X
    have : Mono (colimit.desc _ c) := by
      rw [hS₁.isSeparating.mono_iff]
      let Φ := CostructuredArrow.proj
        (P.colimitsCardinalClosure κ).ι X ⋙ (P.colimitsCardinalClosure κ).ι
      intro G hG (g₁ : G ⟶ colimit Φ) (g₂ : G ⟶ colimit Φ)
        (h : g₁ ≫ colimit.desc Φ c = g₂ ≫ colimit.desc Φ c)
      have : IsCardinalPresentable G κ := hS₂ _ hG
      obtain ⟨j, φ₁, φ₂, rfl, rfl⟩ :
          ∃ (j :  CostructuredArrow (P.colimitsCardinalClosure κ).ι X)
            (φ₁ φ₂ : G ⟶ Φ.obj j), φ₁ ≫ colimit.ι _ _ = g₁ ∧ φ₂ ≫ colimit.ι _ _ = g₂ := by
        obtain ⟨j₁, f₁, hf₁⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₁
        obtain ⟨j₂, f₂, hf₂⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₂
        exact ⟨IsFiltered.max j₁ j₂, f₁ ≫ Φ.map (IsFiltered.leftToMax j₁ j₂),
          f₂ ≫ Φ.map (IsFiltered.rightToMax j₁ j₂), by simpa, by simpa⟩
      simp only [Category.assoc, colimit.ι_desc] at h
      have : (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape WalkingParallelPair := by
        apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        refine .of_le ?_ (Cardinal.IsRegular.aleph0_le Fact.out)
        simp only [hasCardinalLT_aleph0_iff]
        infer_instance
      let E : (P.colimitsCardinalClosure κ).FullSubcategory :=
        ⟨coequalizer φ₁ φ₂, by
          apply ObjectProperty.prop_colimit
          rintro (_ | _)
          · exact P.le_colimitsCardinalClosure _ _ hG
          · exact j.left.2⟩
      let a : (P.colimitsCardinalClosure κ).ι.obj E ⟶ X := coequalizer.desc (c.ι.app j) h
      let ψ : j ⟶ CostructuredArrow.mk a :=
        CostructuredArrow.homMk (coequalizer.π _ _) (coequalizer.π_desc _ _)
      rw [← colimit.w Φ ψ]
      apply coequalizer.condition_assoc
    have : IsIso (colimit.desc _ c) := hS₁.isIso_of_mono _ (fun g φ ↦ by
      let γ : CostructuredArrow (P.colimitsCardinalClosure κ).ι X :=
        CostructuredArrow.mk (Y := ⟨g.1, P.le_colimitsCardinalClosure _ _ g.2⟩) (by exact φ)
      refine ⟨colimit.ι (CostructuredArrow.proj _ _ ⋙ (P.colimitsCardinalClosure κ).ι) γ, ?_⟩
      dsimp
      rw [colimit.ι_desc]
      rfl)
    exact ⟨CanonicalColimis.ofIsIso _ _⟩

lemma ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
    [LocallySmall.{w} C] (P : ObjectProperty C) (hP : P ≤ isCardinalPresentable C κ) :
    P.colimitsCardinalClosure κ ≤ isCardinalPresentable C κ :=
  P.colimitsCardinalClosure_le κ
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ) hP

lemma IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : IsStrongGenerator P)
    (hS₂ : P ≤ isCardinalPresentable C κ) :
    isCardinalPresentable C κ = P.colimitsCardinalClosure κ := by
  refine le_antisymm ?_ (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
  have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
  intro X hX
  rw [isCardinalPresentable_iff] at hX
  rw [← (P.colimitsCardinalClosure κ).retractClosure_eq_self ]
  obtain ⟨j, φ, hφ⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    ((P.colimitsCardinalClosure κ).ι.canonicalColimitOfIsDense X) (𝟙 X)
  exact ⟨_, j.left.2, ⟨{ i := _, r := _, retract := hφ }⟩⟩

namespace IsCardinalLocallyPresentable

variable (C κ) in
lemma iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P), IsStrongGenerator P ∧
        P ≤ isCardinalPresentable C κ := by
  refine ⟨fun _ ↦ ?_, fun ⟨P, _, hS₁, hS₂⟩ ↦ ?_⟩
  · obtain ⟨ι, G, hG⟩ := HasCardinalFilteredGenerators.exists_generators C κ
    refine ⟨Set.range G, inferInstanceAs (Small.{w} (Set.range G)), hG.isStrongGenerator, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hG.isCardinalPresentable i
  · have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
    have := HasCardinalFilteredGenerators.of_essentiallySmall_of_dense
      (P.colimitsCardinalClosure κ) (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
    constructor

variable [IsCardinalLocallyPresentable C κ]

variable (C) in
lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular]
    (h : κ ≤ κ') :
    IsCardinalLocallyPresentable C κ' := by
  rw [iff_exists_isStrongGenerator]
  obtain ⟨S, _, h₁, h₂⟩ := (iff_exists_isStrongGenerator C κ).1 inferInstance
  exact ⟨S, inferInstance, h₁, by
    refine h₂.trans (isCardinalPresentable_monotone _ h)⟩

instance : ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  obtain ⟨ι, G, hG⟩ := HasCardinalFilteredGenerators.exists_generators C κ
  have : ObjectProperty.Small.{w} (Set.range G) :=
    inferInstanceAs (Small.{w} (Set.range G))
  rw [hG.isStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable (κ := κ)
    (by rintro _ ⟨i, rfl⟩; exact hG.isCardinalPresentable i)]
  infer_instance

instance : (isCardinalPresentable C κ).ι.IsDense := by
  obtain ⟨ι, G, hG⟩ := HasCardinalFilteredGenerators.exists_generators C κ
  have : ObjectProperty.Small.{w} (Set.range G) :=
    inferInstanceAs (Small.{w} (Set.range G))
  rw [hG.isStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable (κ := κ)
    (by rintro _ ⟨i, rfl⟩; exact hG.isCardinalPresentable i)]
  refine IsStrongGenerator.isDense_colimitsCardinalClosure_ι
    (hG.isStrongGenerator) (by rintro _ ⟨_, rfl⟩; apply hG.isCardinalPresentable)

end IsCardinalLocallyPresentable

namespace IsLocallyPresentable

instance essentiallySmall_isCardinalPresentable
    [IsLocallyPresentable.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  obtain ⟨κ₀, _, _⟩  := IsLocallyPresentable.exists_cardinal.{w} C
  by_cases h : κ₀ ≤ κ
  · have := IsCardinalLocallyPresentable.of_le C h
    infer_instance
  · simp only [not_le] at h
    exact ObjectProperty.EssentiallySmall.of_le (isCardinalPresentable_monotone C h.le)

end IsLocallyPresentable

end CategoryTheory
