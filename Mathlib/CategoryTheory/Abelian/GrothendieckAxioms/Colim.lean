/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected

/-!
# Exactness of colimits

In this file, we shall study exactness properties of colimits.
First, we translate the assumption that `colim : (J ⥤ C) ⥤ C`
preserves monomorphisms (or epimorphisms) into statements
involving arbitrary cocones instead of the ones given by
the colimit API. We also show that when an inductive system
involves only monomorphisms, then the "inclusion" morphism
into the colimit is also a monomorphism (assuming `J`
is filtered and `C` satisfies AB5).

-/

universe v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

namespace Limits

/-- Assume that `colim : (J ⥤ C) ⥤ C` preserves monomorphisms, and
`φ : X₁ ⟶ X₂` is a monomorphism in `J ⥤ C`, then if `f : c₁.pt ⟶ c₂.pt` is a morphism
between the points of colimit cocones for `X₁` and `X₂` in such a way that `f`
idenfities to `colim.map φ`, then `f` is a monomorphism. -/
lemma colim.map_mono' [HasColimitsOfShape J C]
    [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms]
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [Mono φ]
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Mono f := by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    (inferInstanceAs (Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ by
      dsimp
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
        colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
        IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]))

/-- Assume that `φ : X₁ ⟶ X₂` is a natural transformation in `J ⥤ C` which
consists of epimorphisms, then if `f : c₁.pt ⟶ c₂.pt` is a morphism
between the points of cocones `c₁` and `c₂` for `X₁` and `X₂`, in such
a way that `c₂` is colimit and `f` is compatible with `φ`, then `f` is an epimorphism. -/
lemma colim.map_epi'
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [∀ j, Epi (φ.app j)]
    (c₁ : Cocone X₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Epi f where
  left_cancellation {Z} g₁ g₂ h := hc₂.hom_ext (fun j ↦ by
    rw [← cancel_epi (φ.app j), ← reassoc_of% hf, h, reassoc_of% hf])

attribute [local instance] IsFiltered.isConnected

/-- Assume that a functor `X : J ⥤ C` maps any morphism to a monomorphism,
that `J` is filtered. Then the "inclusion" map `c.ι.app j₀` of a colimit cocone for `X`
is a monomorphism if `colim : (Under j₀ ⥤ C) ⥤ C` preserves monomorphisms
(e.g. when `C` satisfies AB5). -/
lemma IsColimit.mono_ι_app_of_isFiltered
    {X : J ⥤ C} [∀ (j j' : J) (φ : j ⟶ j'), Mono (X.map φ)]
    {c : Cocone X} (hc : IsColimit c) [IsFiltered J] (j₀ : J)
    [HasColimitsOfShape (Under j₀) C]
    [(colim : (Under j₀ ⥤ C) ⥤ C).PreservesMonomorphisms] :
    Mono (c.ι.app j₀) := by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c.ι.app j₀) (by aesop_cat)

end Limits

end CategoryTheory
