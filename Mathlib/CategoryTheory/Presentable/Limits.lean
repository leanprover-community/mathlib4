/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Colimits of presentable objects

In this file, we show that `κ`-accessible functors (to the category of types)
are stable under limits indexed by a category `K` such that
`HasCardinalLT (Arrow K) κ`.
In particular, `κ`-presentable objects are stable by colimits indexed
by a category `K` such that `HasCardinalLT (Arrow K) κ`.

-/

universe w w' v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace Functor

namespace Accessible

namespace Limits

section

variable {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'}
  (c : Cone F) (hc : ∀ (Y : C), IsLimit (((evaluation _ _).obj Y).mapCone c))
  (κ : Cardinal.{w}) [Fact κ.IsRegular]
  (hK : HasCardinalLT (Arrow K) κ)
  {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
  {X : J ⥤ C} (cX : Cocone X)
  (hF : ∀ (k : K), IsColimit ((F.obj k).mapCocone cX))

namespace isColimitMapCocone

include hc hF hK

lemma surjective (x : c.pt.obj cX.pt) :
    ∃ (j : J) (x' : c.pt.obj (X.obj j)), x = (c.pt.mapCocone cX).ι.app j x' := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨y, hy⟩ := (Types.isLimitEquivSections (hc cX.pt)).symm.surjective x
  obtain ⟨j₀, z, hz⟩ : ∃ (j₀ : J) (z : (k : K) → (F.obj k).obj (X.obj j₀)),
      ∀ (k : K), y.1 k = (F.obj k).map (cX.ι.app j₀) (z k) := by
    have H (k : K) := Types.jointly_surjective_of_isColimit (hF k) (y.1 k)
    let j (k : K) : J := (H k).choose
    let z (k : K) : (F.obj k).obj (X.obj (j k)) := (H k).choose_spec.choose
    have hz (k : K) : (F.obj k).map (cX.ι.app (j k)) (z k) = y.1 k :=
      (H k).choose_spec.choose_spec
    exact ⟨IsCardinalFiltered.max j (hasCardinalLT_of_hasCardinalLT_arrow hK),
      fun k ↦ (F.obj k).map (X.map (IsCardinalFiltered.toMax j _ k)) (z k),
        fun k ↦ by rw [← hz, ← FunctorToTypes.map_comp_apply, cX.w]⟩
  obtain ⟨j₁, α, hα⟩ : ∃ (j₁ : J) (α : j₀ ⟶ j₁), ∀ ⦃k k' : K⦄ (φ : k ⟶ k'),
      (F.obj k').map (X.map α) ((F.map φ).app _ (z k)) =
        (F.obj k').map (X.map α) (z k') := by
    have H {k k' : K} (φ : k ⟶ k') :=
      (Types.FilteredColimit.isColimit_eq_iff' (ht := hF k')
        (x := (F.map φ).app _ (z k)) (y := z k')).1 (by
          dsimp
          simpa only [← FunctorToTypes.naturality, ← hz] using y.2 φ)
    let j {k k' : K} (φ : k ⟶ k') : J := (H φ).choose
    let g {k k' : K} (φ : k ⟶ k') : j₀ ⟶ j φ := (H φ).choose_spec.choose
    have hg {k k' : K} (φ : k ⟶ k') :
        (F.obj k').map (X.map (g φ)) ((F.map φ).app _ (z k)) =
          (F.obj k').map (X.map (g φ)) (z k') := (H φ).choose_spec.choose_spec
    obtain ⟨j₁, α, β, hα⟩ : ∃ (j₁ : J) (α : j₀ ⟶ j₁)
        (β : ∀ ⦃k k' : K⦄ (φ : k ⟶ k'), j φ ⟶ j₁),
        ∀ ⦃k k' : K⦄ (φ : k ⟶ k'), α = g φ ≫ β φ := by
      let j'' (f : Arrow K) : J := j f.hom
      let ψ (f : Arrow K) : j₀ ⟶ IsCardinalFiltered.max j'' hK :=
        g f.hom ≫ IsCardinalFiltered.toMax j'' hK f
      refine ⟨IsCardinalFiltered.coeq ψ hK, IsCardinalFiltered.toCoeq ψ hK,
        fun k k' φ ↦ IsCardinalFiltered.toMax j'' hK φ ≫ IsCardinalFiltered.coeqHom ψ hK,
        fun k k' φ ↦ ?_⟩
      simpa [ψ] using (IsCardinalFiltered.coeq_condition ψ hK (Arrow.mk φ)).symm
    exact ⟨j₁, α, fun k k' φ ↦ by simp [hα φ, hg]⟩
  let s : (F ⋙ (evaluation C (Type w')).obj (X.obj j₁)).sections :=
    { val k := (F.obj k).map (X.map α) (z k)
      property {k k'} φ := by
        dsimp
        rw [FunctorToTypes.naturality, ← hα φ] }
  refine ⟨j₁, (Types.isLimitEquivSections (hc (X.obj j₁))).symm s, ?_⟩
  apply (Types.isLimitEquivSections (hc cX.pt)).injective
  rw [← hy, Equiv.apply_symm_apply]
  ext k
  have h₁ := Types.isLimitEquivSections_apply (hc cX.pt) k
    (c.pt.map (cX.ι.app j₁) ((Types.isLimitEquivSections (hc (X.obj j₁))).symm s))
  have h₂ := Types.isLimitEquivSections_symm_apply (hc (X.obj j₁)) s k
  dsimp at h₁ h₂ ⊢
  rw [h₁, hz, FunctorToTypes.naturality, h₂, ← FunctorToTypes.map_comp_apply, cX.w]

lemma injective (j : J) (x₁ x₂ : c.pt.obj (X.obj j))
    (h : c.pt.map (cX.ι.app j) x₁ = c.pt.map (cX.ι.app j) x₂) :
    ∃ (j' : J) (α : j ⟶ j'),
    c.pt.map (X.map α) x₁ = c.pt.map (X.map α) x₂ := by
  have := isFiltered_of_isCardinalFiltered J κ
  let y₁ := Types.isLimitEquivSections (hc (X.obj j)) x₁
  let y₂ := Types.isLimitEquivSections (hc (X.obj j)) x₂
  have hy₁ : (Types.isLimitEquivSections (hc (X.obj j))).symm y₁ = x₁ := by simp [y₁]
  have hy₂ : (Types.isLimitEquivSections (hc (X.obj j))).symm y₂ = x₂ := by simp [y₂]
  have H (k : K) := (Types.FilteredColimit.isColimit_eq_iff' (ht := hF k)
    (x := y₁.1 k) (y := y₂.1 k)).1 (by
      simp only [y₁, y₂, Types.isLimitEquivSections_apply]
      dsimp
      simp only [← FunctorToTypes.naturality, h])
  let j₁ (k : K) : J := (H k).choose
  let f (k : K) : j ⟶ j₁ k := (H k).choose_spec.choose
  have hf (k : K) : (F.obj k).map (X.map (f k)) (y₁.1 k) =
      (F.obj k).map (X.map (f k)) (y₂.1 k) :=
    (H k).choose_spec.choose_spec
  have hK' := hasCardinalLT_of_hasCardinalLT_arrow hK
  let ψ (k : K) : j ⟶ IsCardinalFiltered.max j₁ hK' :=
    f k ≫ IsCardinalFiltered.toMax j₁ hK' k
  refine ⟨IsCardinalFiltered.coeq ψ hK', IsCardinalFiltered.toCoeq ψ hK', ?_⟩
  apply (Types.isLimitEquivSections (hc _)).injective
  ext k
  simp only [Types.isLimitEquivSections_apply, ← hy₁, ← hy₂]
  have h₁ := Types.isLimitEquivSections_symm_apply (hc (X.obj j)) y₁ k
  have h₂ := Types.isLimitEquivSections_symm_apply (hc (X.obj j)) y₂ k
  dsimp at h₁ h₂ ⊢
  simp only [FunctorToTypes.naturality, h₁, h₂,
    ← IsCardinalFiltered.coeq_condition ψ hK' k,
    map_comp, FunctorToTypes.map_comp_apply, ψ, hf]

end isColimitMapCocone

/-- Auxiliary definition for `isCardinalAccessible_of_isLimit`. -/
noncomputable def isColimitMapCocone : IsColimit (c.pt.mapCocone cX) := by
  have := isFiltered_of_isCardinalFiltered J κ
  apply Types.FilteredColimit.isColimitOf'
  · exact isColimitMapCocone.surjective c hc κ hK cX hF
  · exact isColimitMapCocone.injective c hc κ hK cX hF

end

end Limits

end Accessible

lemma isCardinalAccessible_of_isLimit {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'}
    (c : Cone F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasLimitsOfShape K (Type w')] (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, (F.obj k).IsCardinalAccessible κ] :
    c.pt.IsCardinalAccessible κ where
  preservesColimitOfShape {J _ _} := ⟨fun {X} ↦ ⟨fun {cX} hcX ↦ by
    have := fun k ↦ preservesColimitsOfShape_of_isCardinalAccessible (F.obj k) κ J
    exact ⟨Accessible.Limits.isColimitMapCocone c
      (fun Y ↦ isLimitOfPreserves ((evaluation C (Type w')).obj Y) hc) κ hK cX
      (fun k ↦ isColimitOfPreserves (F.obj k) hcX)⟩⟩⟩

end Functor

/-- In case `C` is locally `w`-small, use `isCardinalPresentable_of_isColimit`. -/
lemma isCardinalPresentable_of_isColimit'
    {K : Type u'} [Category.{v'} K] {Y : K ⥤ C}
    (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasLimitsOfShape Kᵒᵖ (Type v)] (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, IsCardinalPresentable (Y.obj k) κ] :
    IsCardinalPresentable c.pt κ := by
  have (k : Kᵒᵖ) : ((Y.op ⋙ coyoneda).obj k).IsCardinalAccessible κ := by
    dsimp; infer_instance
  exact Functor.isCardinalAccessible_of_isLimit
    (coyoneda.mapCone c.op) (isLimitOfPreserves _ hc.op) κ (by simpa)

lemma isCardinalPresentable_of_isColimit [LocallySmall.{w} C]
    {K : Type u'} [Category.{v'} K] [HasLimitsOfShape Kᵒᵖ (Type w)] {Y : K ⥤ C}
    (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, IsCardinalPresentable (Y.obj k) κ] :
    IsCardinalPresentable c.pt κ := by
  let e := ShrinkHoms.equivalence.{w} C
  have (k : K) : IsCardinalPresentable ((Y ⋙ e.functor).obj k) κ := by
    dsimp; infer_instance
  rw [← isCardinalPresentable_iff_of_isEquivalence c.pt κ e.functor]
  exact isCardinalPresentable_of_isColimit' _
    (isColimitOfPreserves e.functor hc) κ hK

variable (C) in
lemma isClosedUnderColimitsOfShape_isCardinalPresentable [LocallySmall.{w} C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular]
    {J : Type u'} [Category.{v'} J] [HasLimitsOfShape Jᵒᵖ (Type w)]
    (hJ : HasCardinalLT (Arrow J) κ) :
    (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    have := hX.prop_diag_obj
    simp only [isCardinalPresentable_iff] at this ⊢
    exact isCardinalPresentable_of_isColimit _ hX.isColimit κ hJ

end CategoryTheory
