/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Presentable.Basic

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
  {X : J ⥤ C} (cX : Cocone X) (hcX : IsColimit cX)
  (hF : ∀ (k : K), IsColimit ((F.obj k).mapCocone cX))

noncomputable def isColimitMapCocone : IsColimit (c.pt.mapCocone cX) := by
  have := isFiltered_of_isCardinalDirected J κ
  have := hcX
  apply Types.FilteredColimit.isColimitOf
  · intro x
    obtain ⟨y, hy⟩ := (Types.isLimitEquivSections (hc cX.pt)).symm.surjective x
    have H := fun k ↦ Types.jointly_surjective_of_isColimit (hF k) (y.1 k)
    dsimp at H
    let j (k : K) : J := (H k).choose
    let z (k : K) : (F.obj k).obj (X.obj (j k)) := (H k).choose_spec.choose
    have hz (k : K) : (F.obj k).map (cX.ι.app (j k)) (z k) = y.1 k :=
      (H k).choose_spec.choose_spec
    have H' {k k' : K} (φ : k ⟶ k') :=
      (Types.FilteredColimit.isColimit_eq_iff (ht := hF k')
         (xi := (F.map φ).app _ (z k)) (xj := z k')).1 (by
          dsimp
          simpa only [← FunctorToTypes.naturality, hz] using y.2 φ)
    dsimp at H'
    have hK' := hasCardinalLT_of_hasCardinalLT_arrow hK
    let j₀ : J := IsCardinalFiltered.max j hK'
    let α (k : K) : j k ⟶ j₀ := IsCardinalFiltered.toMax j hK' k
    have j₁ : J := sorry
    have β : j₀ ⟶ j₁ := sorry
    have hβ {k k'} (φ : k ⟶ k') :
      (F.obj k').map (X.map β) ((F.obj k').map (X.map (α k)) ((F.map φ).app (X.obj (j k)) (z k))) =
      (F.obj k').map (X.map β) ((F.obj k').map (X.map (α k')) (z k')) := sorry
    let s : (F ⋙ (evaluation C (Type w')).obj (X.obj j₁)).sections :=
      { val k := (F.obj k).map (X.map (α k ≫ β)) (z k)
        property {k k'} φ := by
          dsimp
          simp only [FunctorToTypes.naturality, Functor.map_comp,
            types_comp_apply]
          apply hβ }
    refine ⟨j₁, (Types.isLimitEquivSections (hc (X.obj j₁))).symm s, ?_⟩
    apply (Types.isLimitEquivSections (hc cX.pt)).injective
    rw [← hy, Equiv.apply_symm_apply]
    ext k
    have h₁ := Types.isLimitEquivSections_apply (hc cX.pt) k
      (c.pt.map (cX.ι.app j₁) ((Types.isLimitEquivSections (hc (X.obj j₁))).symm s))
    have h₂ := Types.isLimitEquivSections_symm_apply (hc (X.obj j₁)) s k
    dsimp at h₁ h₂ ⊢
    rw [h₁, ← hz k, FunctorToTypes.naturality, h₂, ← FunctorToTypes.map_comp_apply, cX.w]
  · sorry

end

end Limits

end Accessible

lemma accessible_of_isLimit {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'}
    (c : Cone F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hK : HasCardinalLT (Arrow K) κ)
    [HasLimitsOfShape K (Type w')]
    [∀ k, (F.obj k).IsAccessible κ] :
    c.pt.IsAccessible κ where
  preservesColimitOfShape {J _ _} := ⟨fun {X} ↦ ⟨fun {cX} hcX ↦ by
    have := fun k ↦ preservesColimitsOfShape_of_isAccessible (F.obj k) κ J
    exact ⟨Accessible.Limits.isColimitMapCocone c
      (fun Y ↦ isLimitOfPreserves ((evaluation C (Type w')).obj Y) hc) κ hK cX hcX
      (fun k ↦ isColimitOfPreserves (F.obj k) hcX)⟩⟩⟩


end Functor

lemma isPresentable_of_isColimit
    {K : Type u'} [Category.{v'} K] {Y : K ⥤ C}
    (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hK : HasCardinalLT (Arrow K) κ)
    [HasLimitsOfShape Kᵒᵖ (Type v)]
    [∀ k, IsPresentable (Y.obj k) κ] :
    IsPresentable c.pt κ := by
  have : ∀ (k : Kᵒᵖ), ((Y.op ⋙ coyoneda).obj k).IsAccessible κ := fun k ↦ by
    dsimp
    infer_instance
  exact Functor.accessible_of_isLimit
    (coyoneda.mapCone c.op) (isLimitOfPreserves _ hc.op) κ (by simpa)

end CategoryTheory
