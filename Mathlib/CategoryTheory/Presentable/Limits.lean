/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types
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

namespace Limits

namespace Types

namespace FilteredColimit

variable {J : Type u} [Category.{v} J] [IsFiltered J] {F : J ⥤ Type w}
  (c : Cocone F)

def isColimit_mk (hc₁ : ∀ (x : c.pt), ∃ (j : J) (y : F.obj j), c.ι.app j y = x)
    (hc₂ : ∀ (j : J) (y₁ y₂ : F.obj j) (hy : c.ι.app j y₁ = c.ι.app j y₂),
      ∃ (j' : J) (k : j ⟶ j'), F.map k y₁ = F.map k y₂) :
    IsColimit c := by
  have : IsFiltered J := inferInstance
  sorry

end FilteredColimit

end Types

end Limits

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

def isColimitMapCocone : IsColimit (c.pt.mapCocone cX) := by
  have := isFiltered_of_isCardinalDirected J κ
  have := hcX
  apply Types.FilteredColimit.isColimit_mk
  · intro x
    obtain ⟨y, hy⟩ := (Types.isLimitEquivSections (hc cX.pt)).symm.surjective x
    have H := fun k ↦ Types.jointly_surjective_of_isColimit (hF k) (y.1 k)
    let j (k : K) : J := (H k).choose
    let z (k : K) : (F.obj k).obj (X.obj (j k)) := (H k).choose_spec.choose
    have hz (k : K) : (F.obj k).map (cX.ι.app (j k)) (z k) = y.1 k :=
      (H k).choose_spec.choose_spec
    have hK' := hasCardinalLT_of_hasCardinalLT_arrow hK
    have pif := IsCardinalFiltered.max j hK'
    let j₀ : J := IsCardinalFiltered.max j hK'
    let α (k : K) : j k ⟶ j₀ := IsCardinalFiltered.toMax j hK' k
    have j₁ : J := sorry
    have β : j₀ ⟶ j₁ := sorry
    let s : (F ⋙ (evaluation C (Type w')).obj (X.obj j₁)).sections :=
      { val k := (F.obj k).map (X.map (α k ≫ β)) (z k)
        property {k k'} φ := by
          sorry }
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
