/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Bhavik Mehta, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.limits.preserves.basic
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C → D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category_theory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- A functor `F` preserves limits of `K` (written as `preserves_limit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cone K}, IsLimit c → IsLimit (F.mapCone c)
#align category_theory.limits.preserves_limit CategoryTheory.Limits.PreservesLimit

/-- A functor `F` preserves colimits of `K` (written as `preserves_colimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cocone K}, IsColimit c → IsColimit (F.mapCocone c)
#align category_theory.limits.preserves_colimit CategoryTheory.Limits.PreservesColimit

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  PreservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance
#align category_theory.limits.preserves_limits_of_shape CategoryTheory.Limits.PreservesLimitsOfShape

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  PreservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance
#align category_theory.limits.preserves_colimits_of_shape CategoryTheory.Limits.PreservesColimitsOfShape

-- This should be used with explicit universe variables.
/-- `preserves_limits_of_size.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[category.{v} J]`. -/
@[nolint check_univs]
class PreservesLimitsOfSize (F : C ⥤ D) where
  PreservesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    infer_instance
#align category_theory.limits.preserves_limits_of_size CategoryTheory.Limits.PreservesLimitsOfSize

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F
#align category_theory.limits.preserves_limits CategoryTheory.Limits.PreservesLimits

-- This should be used with explicit universe variables.
/-- `preserves_colimits_of_size.{v u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[category.{v} J]`. -/
@[nolint check_univs]
class PreservesColimitsOfSize (F : C ⥤ D) where
  PreservesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    infer_instance
#align category_theory.limits.preserves_colimits_of_size CategoryTheory.Limits.PreservesColimitsOfSize

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesColimits (F : C ⥤ D) :=
  PreservesColimitsOfSize.{v₂, v₂} F
#align category_theory.limits.preserves_colimits CategoryTheory.Limits.PreservesColimits

attribute [instance]
  preserves_limits_of_shape.preserves_limit preserves_limits_of_size.preserves_limits_of_shape preserves_colimits_of_shape.preserves_colimit preserves_colimits_of_size.preserves_colimits_of_shape

-- see Note [lower instance priority]
/-- A convenience function for `preserves_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  PreservesLimit.preserves t
#align category_theory.limits.is_limit_of_preserves CategoryTheory.Limits.isLimitOfPreserves

/--
A convenience function for `preserves_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  PreservesColimit.preserves t
#align category_theory.limits.is_colimit_of_preserves CategoryTheory.Limits.isColimitOfPreserves

instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (PreservesLimit K F) :=
  by constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr
#align category_theory.limits.preserves_limit_subsingleton CategoryTheory.Limits.preservesLimit_subsingleton

instance preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesColimit K F) := by constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr
#align category_theory.limits.preserves_colimit_subsingleton CategoryTheory.Limits.preservesColimit_subsingleton

instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) :=
  by
  constructor
  intros
  cases a
  cases b
  congr
#align category_theory.limits.preserves_limits_of_shape_subsingleton CategoryTheory.Limits.preservesLimitsOfShape_subsingleton

instance preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) :=
  by
  constructor
  intros
  cases a
  cases b
  congr
#align category_theory.limits.preserves_colimits_of_shape_subsingleton CategoryTheory.Limits.preservesColimitsOfShape_subsingleton

instance preserves_limits_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) :=
  by
  constructor
  intros
  cases a
  cases b
  cc
#align category_theory.limits.preserves_limits_subsingleton CategoryTheory.Limits.preserves_limits_subsingleton

instance preserves_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfSize.{w', w} F) :=
  by
  constructor
  intros
  cases a
  cases b
  cc
#align category_theory.limits.preserves_colimits_subsingleton CategoryTheory.Limits.preserves_colimits_subsingleton

instance idPreservesLimits : PreservesLimitsOfSize.{w', w} (𝟭 C)
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.lift ⟨s.x, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;>
              exact h.uniq _ m w⟩⟩ }
#align category_theory.limits.id_preserves_limits CategoryTheory.Limits.idPreservesLimits

instance idPreservesColimits : PreservesColimitsOfSize.{w', w} (𝟭 C)
    where PreservesColimitsOfShape J 𝒥 :=
    {
      PreservesColimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.desc ⟨s.x, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;>
              exact h.uniq _ m w⟩⟩ }
#align category_theory.limits.id_preserves_colimits CategoryTheory.Limits.idPreservesColimits

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

attribute [local elab_without_expected_type] preserves_limit.preserves preserves_colimit.preserves

instance compPreservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) :=
  ⟨fun c h => PreservesLimit.preserves (PreservesLimit.preserves h)⟩
#align category_theory.limits.comp_preserves_limit CategoryTheory.Limits.compPreservesLimit

instance compPreservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where
#align category_theory.limits.comp_preserves_limits_of_shape CategoryTheory.Limits.compPreservesLimitsOfShape

instance compPreservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where
#align category_theory.limits.comp_preserves_limits CategoryTheory.Limits.compPreservesLimits

instance compPreservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) :=
  ⟨fun c h => PreservesColimit.preserves (PreservesColimit.preserves h)⟩
#align category_theory.limits.comp_preserves_colimit CategoryTheory.Limits.compPreservesColimit

instance compPreservesColimitsOfShape [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J (F ⋙ G) where
#align category_theory.limits.comp_preserves_colimits_of_shape CategoryTheory.Limits.compPreservesColimitsOfShape

instance compPreservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} (F ⋙ G) where
#align category_theory.limits.comp_preserves_colimits CategoryTheory.Limits.compPreservesColimits

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preservesLimitOfPreservesLimitCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F :=
  ⟨fun t' h' => IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩
#align category_theory.limits.preserves_limit_of_preserves_limit_cone CategoryTheory.Limits.preservesLimitOfPreservesLimitCone

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
def preservesLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] :
    PreservesLimit K₂ F
    where preserves c t :=
    by
    apply is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _ _
    have := (is_limit.postcompose_inv_equiv h c).symm t
    apply is_limit.of_iso_limit (is_limit_of_preserves F this)
    refine' cones.ext (iso.refl _) fun j => by tidy
#align category_theory.limits.preserves_limit_of_iso_diagram CategoryTheory.Limits.preservesLimitOfIsoDiagram

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
def preservesLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where preserves c t := IsLimit.mapConeEquiv h (PreservesLimit.preserves t)
#align category_theory.limits.preserves_limit_of_nat_iso CategoryTheory.Limits.preservesLimitOfNatIso

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
def preservesLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where PreservesLimit K := preservesLimitOfNatIso K h
#align category_theory.limits.preserves_limits_of_shape_of_nat_iso CategoryTheory.Limits.preservesLimitsOfShapeOfNatIso

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
def preservesLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G
    where PreservesLimitsOfShape J 𝒥₁ := preserves_limits_of_shape_of_nat_iso h
#align category_theory.limits.preserves_limits_of_nat_iso CategoryTheory.Limits.preservesLimitsOfNatIso

/-- Transfer preservation of limits along a equivalence in the shape. -/
def preservesLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F
    where PreservesLimit K :=
    {
      preserves := fun c t => by
        let equ := e.inv_fun_id_assoc (K ⋙ F)
        have := (is_limit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm
        apply ((is_limit.postcompose_hom_equiv equ _).symm this).ofIsoLimit
        refine' cones.ext (iso.refl _) fun j => _
        · dsimp
          simp [← functor.map_comp] }
#align category_theory.limits.preserves_limits_of_shape_of_equiv CategoryTheory.Limits.preservesLimitsOfShapeOfEquiv

-- See library note [dsimp, simp].
/-- `preserves_limits_of_size_shrink.{w w'} F` tries to obtain `preserves_limits_of_size.{w w'} F`
from some other `preserves_limits_of_size F`.
-/
def preservesLimitsOfSizeShrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F :=
  ⟨fun J hJ => preserves_limits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w₂, w₂'} J).symm F⟩
#align category_theory.limits.preserves_limits_of_size_shrink CategoryTheory.Limits.preservesLimitsOfSizeShrink

/-- Preserving limits at any universe level implies preserving limits in universe `0`. -/
def preservesSmallestLimitsOfPreservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSizeShrink F
#align category_theory.limits.preserves_smallest_limits_of_preserves_limits CategoryTheory.Limits.preservesSmallestLimitsOfPreservesLimits

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preservesColimitOfPreservesColimitCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun t' h' => IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩
#align category_theory.limits.preserves_colimit_of_preserves_colimit_cocone CategoryTheory.Limits.preservesColimitOfPreservesColimitCocone

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preservesColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F] :
    PreservesColimit K₂ F
    where preserves c t :=
    by
    apply is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _ _
    have := (is_colimit.precompose_hom_equiv h c).symm t
    apply is_colimit.of_iso_colimit (is_colimit_of_preserves F this)
    refine' cocones.ext (iso.refl _) fun j => by tidy
#align category_theory.limits.preserves_colimit_of_iso_diagram CategoryTheory.Limits.preservesColimitOfIsoDiagram

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
def preservesColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G
    where preserves c t := IsColimit.mapCoconeEquiv h (PreservesColimit.preserves t)
#align category_theory.limits.preserves_colimit_of_nat_iso CategoryTheory.Limits.preservesColimitOfNatIso

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
def preservesColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where PreservesColimit K := preservesColimitOfNatIso K h
#align category_theory.limits.preserves_colimits_of_shape_of_nat_iso CategoryTheory.Limits.preservesColimitsOfShapeOfNatIso

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
def preservesColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G
    where PreservesColimitsOfShape J 𝒥₁ := preserves_colimits_of_shape_of_nat_iso h
#align category_theory.limits.preserves_colimits_of_nat_iso CategoryTheory.Limits.preservesColimitsOfNatIso

/-- Transfer preservation of colimits along a equivalence in the shape. -/
def preservesColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F
    where PreservesColimit K :=
    {
      preserves := fun c t => by
        let equ := e.inv_fun_id_assoc (K ⋙ F)
        have := (is_colimit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm
        apply ((is_colimit.precompose_inv_equiv equ _).symm this).ofIsoColimit
        refine' cocones.ext (iso.refl _) fun j => _
        · dsimp
          simp [← functor.map_comp] }
#align category_theory.limits.preserves_colimits_of_shape_of_equiv CategoryTheory.Limits.preservesColimitsOfShapeOfEquiv

-- See library note [dsimp, simp].
/--
`preserves_colimits_of_size_shrink.{w w'} F` tries to obtain `preserves_colimits_of_size.{w w'} F`
from some other `preserves_colimits_of_size F`.
-/
def preservesColimitsOfSizeShrink (F : C ⥤ D) [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F :=
  ⟨fun J hJ =>
    preserves_colimits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w₂, w₂'} J).symm F⟩
#align category_theory.limits.preserves_colimits_of_size_shrink CategoryTheory.Limits.preservesColimitsOfSizeShrink

/-- Preserving colimits at any universe implies preserving colimits at universe `0`. -/
def preservesSmallestColimitsOfPreservesColimits (F : C ⥤ D) [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSizeShrink F
#align category_theory.limits.preserves_smallest_colimits_of_preserves_colimits CategoryTheory.Limits.preservesSmallestColimitsOfPreservesColimits

/-- A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cone K}, IsLimit (F.mapCone c) → IsLimit c
#align category_theory.limits.reflects_limit CategoryTheory.Limits.ReflectsLimit

/-- A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cocone K}, IsColimit (F.mapCocone c) → IsColimit c
#align category_theory.limits.reflects_colimit CategoryTheory.Limits.ReflectsColimit

/-- A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  ReflectsLimit : ∀ {K : J ⥤ C}, ReflectsLimit K F := by infer_instance
#align category_theory.limits.reflects_limits_of_shape CategoryTheory.Limits.ReflectsLimitsOfShape

/-- A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  ReflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by infer_instance
#align category_theory.limits.reflects_colimits_of_shape CategoryTheory.Limits.ReflectsColimitsOfShape

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[nolint check_univs]
class ReflectsLimitsOfSize (F : C ⥤ D) where
  ReflectsLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    infer_instance
#align category_theory.limits.reflects_limits_of_size CategoryTheory.Limits.ReflectsLimitsOfSize

/-- A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F
#align category_theory.limits.reflects_limits CategoryTheory.Limits.ReflectsLimits

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[nolint check_univs]
class ReflectsColimitsOfSize (F : C ⥤ D) where
  ReflectsColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    infer_instance
#align category_theory.limits.reflects_colimits_of_size CategoryTheory.Limits.ReflectsColimitsOfSize

/-- A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
abbrev ReflectsColimits (F : C ⥤ D) :=
  ReflectsColimitsOfSize.{v₂, v₂} F
#align category_theory.limits.reflects_colimits CategoryTheory.Limits.ReflectsColimits

/-- A convenience function for `reflects_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c)) [ReflectsLimit K F] :
    IsLimit c :=
  ReflectsLimit.reflects t
#align category_theory.limits.is_limit_of_reflects CategoryTheory.Limits.isLimitOfReflects

/--
A convenience function for `reflects_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
    [ReflectsColimit K F] : IsColimit c :=
  ReflectsColimit.reflects t
#align category_theory.limits.is_colimit_of_reflects CategoryTheory.Limits.isColimitOfReflects

instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr
#align category_theory.limits.reflects_limit_subsingleton CategoryTheory.Limits.reflectsLimit_subsingleton

instance reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (ReflectsColimit K F) := by constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr
#align category_theory.limits.reflects_colimit_subsingleton CategoryTheory.Limits.reflectsColimit_subsingleton

instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) :=
  by
  constructor
  intros
  cases a
  cases b
  congr
#align category_theory.limits.reflects_limits_of_shape_subsingleton CategoryTheory.Limits.reflectsLimitsOfShape_subsingleton

instance reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) :=
  by
  constructor
  intros
  cases a
  cases b
  congr
#align category_theory.limits.reflects_colimits_of_shape_subsingleton CategoryTheory.Limits.reflectsColimitsOfShape_subsingleton

instance reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsLimitsOfSize.{w', w} F) :=
  by
  constructor
  intros
  cases a
  cases b
  cc
#align category_theory.limits.reflects_limits_subsingleton CategoryTheory.Limits.reflects_limits_subsingleton

instance reflects_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfSize.{w', w} F) :=
  by
  constructor
  intros
  cases a
  cases b
  cc
#align category_theory.limits.reflects_colimits_subsingleton CategoryTheory.Limits.reflects_colimits_subsingleton

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitOfReflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [H : ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit
#align category_theory.limits.reflects_limit_of_reflects_limits_of_shape CategoryTheory.Limits.reflectsLimitOfReflectsLimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitOfReflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [H : ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  ReflectsColimitsOfShape.reflectsColimit
#align category_theory.limits.reflects_colimit_of_reflects_colimits_of_shape CategoryTheory.Limits.reflectsColimitOfReflectsColimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitsOfShapeOfReflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [H : ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape
#align category_theory.limits.reflects_limits_of_shape_of_reflects_limits CategoryTheory.Limits.reflectsLimitsOfShapeOfReflectsLimits

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitsOfShapeOfReflectsColimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [H : ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  ReflectsColimitsOfSize.reflectsColimitsOfShape
#align category_theory.limits.reflects_colimits_of_shape_of_reflects_colimits CategoryTheory.Limits.reflectsColimitsOfShapeOfReflectsColimits

instance idReflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C)
    where ReflectsLimitsOfShape J 𝒥 :=
    {
      ReflectsLimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.lift ⟨s.x, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;>
              exact h.uniq _ m w⟩⟩ }
#align category_theory.limits.id_reflects_limits CategoryTheory.Limits.idReflectsLimits

instance idReflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C)
    where ReflectsColimitsOfShape J 𝒥 :=
    {
      ReflectsColimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.desc ⟨s.x, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;>
              exact h.uniq _ m w⟩⟩ }
#align category_theory.limits.id_reflects_colimits CategoryTheory.Limits.idReflectsColimits

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

instance compReflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun c h => ReflectsLimit.reflects (ReflectsLimit.reflects h)⟩
#align category_theory.limits.comp_reflects_limit CategoryTheory.Limits.compReflectsLimit

instance compReflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where
#align category_theory.limits.comp_reflects_limits_of_shape CategoryTheory.Limits.compReflectsLimitsOfShape

instance compReflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where
#align category_theory.limits.comp_reflects_limits CategoryTheory.Limits.compReflectsLimits

instance compReflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) :=
  ⟨fun c h => ReflectsColimit.reflects (ReflectsColimit.reflects h)⟩
#align category_theory.limits.comp_reflects_colimit CategoryTheory.Limits.compReflectsColimit

instance compReflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) where
#align category_theory.limits.comp_reflects_colimits_of_shape CategoryTheory.Limits.compReflectsColimitsOfShape

instance compReflectsColimits [ReflectsColimitsOfSize.{w', w} F]
    [ReflectsColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} (F ⋙ G) where
#align category_theory.limits.comp_reflects_colimits CategoryTheory.Limits.compReflectsColimits

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
def preservesLimitOfReflectsOfPreserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun c h => by
    apply is_limit_of_reflects G
    apply is_limit_of_preserves (F ⋙ G) h⟩
#align category_theory.limits.preserves_limit_of_reflects_of_preserves CategoryTheory.Limits.preservesLimitOfReflectsOfPreserves

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
def preservesLimitsOfShapeOfReflectsOfPreserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F
    where PreservesLimit K := preservesLimitOfReflectsOfPreserves F G
#align category_theory.limits.preserves_limits_of_shape_of_reflects_of_preserves CategoryTheory.Limits.preservesLimitsOfShapeOfReflectsOfPreserves

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
def preservesLimitsOfReflectsOfPreserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F
    where PreservesLimitsOfShape J 𝒥₁ := preserves_limits_of_shape_of_reflects_of_preserves F G
#align category_theory.limits.preserves_limits_of_reflects_of_preserves CategoryTheory.Limits.preservesLimitsOfReflectsOfPreserves

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
def reflectsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F
    where reflects c t :=
    by
    apply is_limit.postcompose_inv_equiv h c (is_limit_of_reflects F _)
    apply ((is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _).symm t).ofIsoLimit _
    exact cones.ext (iso.refl _) (by tidy)
#align category_theory.limits.reflects_limit_of_iso_diagram CategoryTheory.Limits.reflectsLimitOfIsoDiagram

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
def reflectsLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where reflects c t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)
#align category_theory.limits.reflects_limit_of_nat_iso CategoryTheory.Limits.reflectsLimitOfNatIso

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
def reflectsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where ReflectsLimit K := reflectsLimitOfNatIso K h
#align category_theory.limits.reflects_limits_of_shape_of_nat_iso CategoryTheory.Limits.reflectsLimitsOfShapeOfNatIso

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
def reflectsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G
    where ReflectsLimitsOfShape J 𝒥₁ := reflects_limits_of_shape_of_nat_iso h
#align category_theory.limits.reflects_limits_of_nat_iso CategoryTheory.Limits.reflectsLimitsOfNatIso

/-- Transfer reflection of limits along a equivalence in the shape. -/
def reflectsLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F
    where ReflectsLimit K :=
    {
      reflects := fun c t => by
        apply is_limit.of_whisker_equivalence e
        apply is_limit_of_reflects F
        apply is_limit.of_iso_limit _ (functor.map_cone_whisker _).symm
        exact is_limit.whisker_equivalence t _ }
#align category_theory.limits.reflects_limits_of_shape_of_equiv CategoryTheory.Limits.reflectsLimitsOfShapeOfEquiv

/-- `reflects_limits_of_size_shrink.{w w'} F` tries to obtain `reflects_limits_of_size.{w w'} F`
from some other `reflects_limits_of_size F`.
-/
def reflectsLimitsOfSizeShrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F :=
  ⟨fun J hJ => reflects_limits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w₂, w₂'} J).symm F⟩
#align category_theory.limits.reflects_limits_of_size_shrink CategoryTheory.Limits.reflectsLimitsOfSizeShrink

/-- Reflecting limits at any universe implies reflecting limits at universe `0`. -/
def reflectsSmallestLimitsOfReflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSizeShrink F
#align category_theory.limits.reflects_smallest_limits_of_reflects_limits CategoryTheory.Limits.reflectsSmallestLimitsOfReflectsLimits

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/
def reflectsLimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [ReflectsIsomorphisms G]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G
    where reflects c t := by
    apply is_limit.of_point_iso (limit.is_limit F)
    change is_iso ((cones.forget _).map ((limit.is_limit F).liftConeMorphism c))
    apply (cones.forget F).map_isIso _
    apply is_iso_of_reflects_iso _ (cones.functoriality F G)
    refine' t.hom_is_iso (is_limit_of_preserves G (limit.is_limit F)) _
#align category_theory.limits.reflects_limit_of_reflects_isomorphisms CategoryTheory.Limits.reflectsLimitOfReflectsIsomorphisms

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
def reflectsLimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G
    where ReflectsLimit F := reflectsLimitOfReflectsIsomorphisms F G
#align category_theory.limits.reflects_limits_of_shape_of_reflects_isomorphisms CategoryTheory.Limits.reflectsLimitsOfShapeOfReflectsIsomorphisms

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
def reflectsLimitsOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] : ReflectsLimitsOfSize.{w', w} G
    where ReflectsLimitsOfShape J 𝒥₁ := reflects_limits_of_shape_of_reflects_isomorphisms
#align category_theory.limits.reflects_limits_of_reflects_isomorphisms CategoryTheory.Limits.reflectsLimitsOfReflectsIsomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
def preservesColimitOfReflectsOfPreserves [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun c h => by
    apply is_colimit_of_reflects G
    apply is_colimit_of_preserves (F ⋙ G) h⟩
#align category_theory.limits.preserves_colimit_of_reflects_of_preserves CategoryTheory.Limits.preservesColimitOfReflectsOfPreserves

/-- If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
def preservesColimitsOfShapeOfReflectsOfPreserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F
    where PreservesColimit K := preservesColimitOfReflectsOfPreserves F G
#align category_theory.limits.preserves_colimits_of_shape_of_reflects_of_preserves CategoryTheory.Limits.preservesColimitsOfShapeOfReflectsOfPreserves

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
def preservesColimitsOfReflectsOfPreserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F
    where PreservesColimitsOfShape J 𝒥₁ := preserves_colimits_of_shape_of_reflects_of_preserves F G
#align category_theory.limits.preserves_colimits_of_reflects_of_preserves CategoryTheory.Limits.preservesColimitsOfReflectsOfPreserves

/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
def reflectsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F
    where reflects c t :=
    by
    apply is_colimit.precompose_hom_equiv h c (is_colimit_of_reflects F _)
    apply ((is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _).symm t).ofIsoColimit _
    exact cocones.ext (iso.refl _) (by tidy)
#align category_theory.limits.reflects_colimit_of_iso_diagram CategoryTheory.Limits.reflectsColimitOfIsoDiagram

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
def reflectsColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G
    where reflects c t := ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)
#align category_theory.limits.reflects_colimit_of_nat_iso CategoryTheory.Limits.reflectsColimitOfNatIso

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
def reflectsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where ReflectsColimit K := reflectsColimitOfNatIso K h
#align category_theory.limits.reflects_colimits_of_shape_of_nat_iso CategoryTheory.Limits.reflectsColimitsOfShapeOfNatIso

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
def reflectsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G
    where ReflectsColimitsOfShape J 𝒥₁ := reflects_colimits_of_shape_of_nat_iso h
#align category_theory.limits.reflects_colimits_of_nat_iso CategoryTheory.Limits.reflectsColimitsOfNatIso

/-- Transfer reflection of colimits along a equivalence in the shape. -/
def reflectsColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F
    where ReflectsColimit K :=
    {
      reflects := fun c t => by
        apply is_colimit.of_whisker_equivalence e
        apply is_colimit_of_reflects F
        apply is_colimit.of_iso_colimit _ (functor.map_cocone_whisker _).symm
        exact is_colimit.whisker_equivalence t _ }
#align category_theory.limits.reflects_colimits_of_shape_of_equiv CategoryTheory.Limits.reflectsColimitsOfShapeOfEquiv

/-- `reflects_colimits_of_size_shrink.{w w'} F` tries to obtain `reflects_colimits_of_size.{w w'} F`
from some other `reflects_colimits_of_size F`.
-/
def reflectsColimitsOfSizeShrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F :=
  ⟨fun J hJ => reflects_colimits_of_shape_of_equiv (UliftHomUliftCategory.equiv.{w₂, w₂'} J).symm F⟩
#align category_theory.limits.reflects_colimits_of_size_shrink CategoryTheory.Limits.reflectsColimitsOfSizeShrink

/-- Reflecting colimits at any universe implies reflecting colimits at universe `0`. -/
def reflectsSmallestColimitsOfReflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsColimitsOfSizeShrink F
#align category_theory.limits.reflects_smallest_colimits_of_reflects_colimits CategoryTheory.Limits.reflectsSmallestColimitsOfReflectsColimits

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/
def reflectsColimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [ReflectsIsomorphisms G]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G
    where reflects c t :=
    by
    apply is_colimit.of_point_iso (colimit.is_colimit F)
    change is_iso ((cocones.forget _).map ((colimit.is_colimit F).descCoconeMorphism c))
    apply (cocones.forget F).map_isIso _
    apply is_iso_of_reflects_iso _ (cocones.functoriality F G)
    refine' (is_colimit_of_preserves G (colimit.is_colimit F)).hom_isIso t _
#align category_theory.limits.reflects_colimit_of_reflects_isomorphisms CategoryTheory.Limits.reflectsColimitOfReflectsIsomorphisms

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
def reflectsColimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G
    where ReflectsColimit F := reflectsColimitOfReflectsIsomorphisms F G
#align category_theory.limits.reflects_colimits_of_shape_of_reflects_isomorphisms CategoryTheory.Limits.reflectsColimitsOfShapeOfReflectsIsomorphisms

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
def reflectsColimitsOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G
    where ReflectsColimitsOfShape J 𝒥₁ := reflects_colimits_of_shape_of_reflects_isomorphisms
#align category_theory.limits.reflects_colimits_of_reflects_isomorphisms CategoryTheory.Limits.reflectsColimitsOfReflectsIsomorphisms

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
def fullyFaithfulReflectsLimits [Full F] [Faithful F] : ReflectsLimitsOfSize.{w, w'} F
    where ReflectsLimitsOfShape J 𝒥₁ :=
    {
      ReflectsLimit := fun K =>
        {
          reflects := fun c t =>
            (is_limit.mk_cone_morphism fun s =>
                (cones.functoriality K F).preimage (t.liftConeMorphism _)) <|
              by
              apply fun s m => (cones.functoriality K F).map_injective _
              rw [functor.image_preimage]
              apply t.uniq_cone_morphism } }
#align category_theory.limits.fully_faithful_reflects_limits CategoryTheory.Limits.fullyFaithfulReflectsLimits

/-- A fully faithful functor reflects colimits. -/
def fullyFaithfulReflectsColimits [Full F] [Faithful F] : ReflectsColimitsOfSize.{w, w'} F
    where ReflectsColimitsOfShape J 𝒥₁ :=
    {
      ReflectsColimit := fun K =>
        {
          reflects := fun c t =>
            (is_colimit.mk_cocone_morphism fun s =>
                (cocones.functoriality K F).preimage (t.descCoconeMorphism _)) <|
              by
              apply fun s m => (cocones.functoriality K F).map_injective _
              rw [functor.image_preimage]
              apply t.uniq_cocone_morphism } }
#align category_theory.limits.fully_faithful_reflects_colimits CategoryTheory.Limits.fullyFaithfulReflectsColimits

end CategoryTheory.Limits

