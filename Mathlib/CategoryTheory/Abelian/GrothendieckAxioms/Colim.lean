/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexFunctorEquiv
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Exactness of colimits

In this file, we shall study exactness properties of colimits.
First, we translate the assumption that `colim : (J ⥤ C) ⥤ C`
preserves monomorphisms (resp. preserves epimorphisms, resp. is exact)
into statements involving arbitrary cocones instead of the ones
given by the colimit API. We also show that when an inductive system
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
identifies to `colim.map φ`, then `f` is a monomorphism. -/
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

section

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] [HasZeroMorphisms C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

/-- Given `S : ShortCompex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`. -/
@[simps]
def colim.mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j ↦ by
    dsimp
    rw [reassoc_of% (hf j), hg j, comp_zero, ← NatTrans.comp_app_assoc, S.zero,
      zero_app, zero_comp]))

variable {S c₂ c₃}

include hc₂ hc₃ hS in
/-- Assuming `HasExactColimitsOfShape J C`, this lemma rephrases the exactness
of the functor `colim : (J ⥤ C) ⥤ C` by saying that if `S : ShortComplex (J ⥤ C)`
is exact, then the short complex obtained by taking the colimits is exact,
where we allow the replacement of the chosen colimit cocones of the
colimit API by arbitrary colimit cocones. -/
lemma colim.exact_mapShortComplex :
    (mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ ?_)) (hc₂.hom_ext (fun j ↦ ?_))
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hg j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]

end

end Limits

namespace MorphismProperty

open Limits

open MorphismProperty

variable (J C) in
lemma isStableUnderColimitsOfShape_monomorphisms
    [HasColimitsOfShape J C] [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms] :
    (monomorphisms C).IsStableUnderColimitsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  have (j : J) : Mono (f.app j) := hf _
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f hc₁ hc₂ _ (by simp)

instance [HasCoproducts.{u'} C] [AB4OfSize.{u'} C] :
    IsStableUnderCoproducts.{u'} (monomorphisms C) where
  isStableUnderCoproductsOfShape _ :=
    isStableUnderColimitsOfShape_monomorphisms _ _

end MorphismProperty

end CategoryTheory

open CategoryTheory Limits

namespace HomologicalComplex

noncomputable def functorEquivalenceInverseCompMapHomologicalComplexColim
    (C : Type*) [Category C] [HasZeroMorphisms C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category J] [HasColimitsOfShape J C] :
    (functorEquivalence C c J).inverse ⋙ colim.mapHomologicalComplex c ≅ colim :=
  NatIso.ofComponents (fun F ↦
    (Hom.isoOfComponents (fun i ↦ IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitOfPreserves (eval C c i) (colimit.isColimit F))) (by aesop_cat))) (by
          intro F G f
          ext i
          dsimp
          ext j
          simp [← comp_f])

lemma quasiIso_functorCategory_iff {C : Type*} [Category C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category J]
    {K L : HomologicalComplex (J ⥤ C) c} (f : K ⟶ L) :
    QuasiIso f ↔
      ∀ (j : J), QuasiIso ((((evaluation J C).obj j).mapHomologicalComplex c).map f) := by
  constructor
  · intro _ j
    infer_instance
  · intro h
    constructor
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, NatTrans.isIso_iff_isIso_app]
    intro j
    apply ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (((evaluation J C).obj j).mapHomologicalComplexHomologyIso c i)).app f)).1
    dsimp
    simp
    infer_instance

lemma isStableUnderColimitsOfShape_quasiIso
    (C : Type*) [Category C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    (HomologicalComplex.quasiIso C c).IsStableUnderColimitsOfShape J := by
  suffices ∀ ⦃F₁ F₂ : J ⥤ HomologicalComplex C c⦄ (f : F₁ ⟶ F₂)
    (hf : (quasiIso C c).functorCategory J f), QuasiIso (colimMap f) by
      intro F₁ F₂ c₁ c₂ h₁ h₂ f hf
      refine ((quasiIso C c).arrow_mk_iso_iff
        (Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₁)
          (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₂)
          (colimit.hom_ext (by simp)))).1 (this f hf)
  intro F₁ F₂ f hf
  have : QuasiIso ((functorEquivalence.inverse C c J).map f) := by
    rwa [quasiIso_functorCategory_iff]
  refine ((quasiIso C c).arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso
    ((functorEquivalenceInverseCompMapHomologicalComplexColim C c J))).app (Arrow.mk f))).1 ?_
  dsimp
  simp only [mem_quasiIso_iff]
  infer_instance

lemma isStableUnderColimitsOfShape_preservesQuasiIso
    (C₁ C₂ : Type*) [Category C₁] [Abelian C₁] [Category C₂] [Abelian C₂]
    {ι₁ ι₂ : Type*} (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)
    (J : Type*) [Category J]
    [HasColimitsOfShape J C₂] [HasExactColimitsOfShape J C₂] :
    ClosedUnderColimitsOfShape J
      (preservesQuasiIso (C₁ := C₁) (C₂ := C₂) (c₁ := c₁) (c₂ := c₂)) := by
  intro F c hc hF K₁ L₁ f hf
  simp only [MorphismProperty.inverseImage_iff]
  have pif := isColimitOfPreserves ((evaluation _ _).obj K₁) hc
  let hcK := isColimitOfPreserves ((evaluation _ _).obj K₁) hc
  let hcL := isColimitOfPreserves ((evaluation _ _).obj L₁) hc
  convert isStableUnderColimitsOfShape_quasiIso C₂ c₂ J _ _ _ _
    hcK hcL (whiskerLeft F ((evaluation _ _).map f)) (fun j ↦ hF j _ hf)
  exact hcK.hom_ext (fun j ↦ by rw [hcK.fac]; simp)

end HomologicalComplex
