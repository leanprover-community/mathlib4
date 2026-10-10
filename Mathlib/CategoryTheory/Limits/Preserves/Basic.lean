/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C ⥤ D "preserves limits" if it
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

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category theory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- A functor `F` preserves limits of `K` (written as `PreservesLimit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cone K} (hc : IsLimit c) : Nonempty (IsLimit (F.mapCone c))

/-- A functor `F` preserves colimits of `K` (written as `PreservesColimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
@[to_dual]
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cocone K} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c))

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
`K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
`K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
@[to_dual]
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesLimitsOfSize.{v, u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[Category.{v} J]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `w, w'` in
-- `PreservesLimitsOfSize`, `PreservesColimitsOfSize`, `ReflectsLimitsOfSize`, and
-- `ReflectsColimitsOfSize` would default to universe output parameters.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
class PreservesLimitsOfSize (F : C ⥤ D) : Prop where
  preservesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesColimitsOfSize.{v, u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[Category.{v} J]`. -/
@[univ_out_params, pp_with_univ, to_dual]
class PreservesColimitsOfSize (F : C ⥤ D) : Prop where
  preservesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    infer_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
@[to_dual
/-- We say that `F` preserves (small) colimits if it sends small
colimit cocones over any diagram to colimit cocones. -/]
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance 100]
  PreservesLimitsOfShape.preservesLimit PreservesLimitsOfSize.preservesLimitsOfShape
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

/-- A convenience function for `PreservesLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
@[to_dual
/-- A convenience function for `PreservesColimit`, which takes the functor as an explicit argument
to guide typeclass resolution.
-/]
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  (PreservesLimit.preserves t).some

@[to_dual]
instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

@[to_dual]
instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

@[to_dual]
instance preservesLimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

@[to_dual]
instance id_preservesLimitsOfSize : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

@[to_dual]
instance [HasLimit K] {F : C ⥤ D} [PreservesLimit K F] : HasLimit (K ⋙ F) where
  exists_limit := ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩

/-- To show that `F` preserves the limit of `K`, we may assume that `K` has a limit. -/
@[to_dual
/-- To show that `F` preserves the colimit of `K`, we may assume that `K` has a colimit. -/]
lemma PreservesLimit.mk' {F : C ⥤ D} (h : HasLimit K → PreservesLimit K F) :
    PreservesLimit K F where
  preserves hc := (h ⟨_, hc⟩).preserves hc

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

@[to_dual]
instance comp_preservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) where
  preserves hc := ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩

@[to_dual]
instance comp_preservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where

@[to_dual]
instance comp_preservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where

end

/-- If F preserves one limit cone for the diagram K,
then it preserves any limit cone for K. -/
@[to_dual
/-- If F preserves one colimit cocone for the diagram K,
then it preserves any colimit cocone for K. -/]
lemma preservesLimit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F where
  preserves h' := ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

@[to_dual]
lemma preservesLimit_iff_isLimit_mapCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) :
    PreservesLimit K F ↔ Nonempty (IsLimit (F.mapCone t)) :=
  ⟨fun _ ↦ ⟨isLimitOfPreserves _ h⟩, fun h' ↦ preservesLimit_of_preserves_limit_cone h h'.some⟩

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
@[to_dual /-- Transfer preservation of colimits along a natural isomorphism in the shape. -/]
lemma preservesLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesLimit K₁ F] : PreservesLimit K₂ F where
  preserves {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cone.ext (Iso.refl _)⟩

@[to_dual]
lemma preservesLimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) :
    PreservesLimit K₁ F ↔ PreservesLimit K₂ F :=
  ⟨fun _ ↦ preservesLimit_of_iso_diagram _ h, fun _ ↦ preservesLimit_of_iso_diagram _ h.symm⟩

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
@[to_dual /-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/]
lemma preservesLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where
  preserves t := ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩

@[to_dual]
lemma preservesLimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimit K F ↔ PreservesLimit K G :=
  ⟨fun _ ↦ preservesLimit_of_natIso _ h, fun _ ↦ preservesLimit_of_natIso _ h.symm⟩

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
@[to_dual
/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/]
lemma preservesLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := preservesLimit_of_natIso K h

@[to_dual]
lemma preservesLimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfShape J F ↔ PreservesLimitsOfShape J G :=
  ⟨fun _ ↦ preservesLimitsOfShape_of_natIso h, fun _ ↦ preservesLimitsOfShape_of_natIso h.symm⟩

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
@[to_dual /-- Transfer preservation of colimits along a natural isomorphism in the functor. -/]
lemma preservesLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  preservesLimitsOfShape := preservesLimitsOfShape_of_natIso h

@[to_dual]
lemma preservesLimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfSize.{w, w'} F ↔ PreservesLimitsOfSize.{w, w'} G :=
  ⟨fun _ ↦ preservesLimits_of_natIso h, fun _ ↦ preservesLimits_of_natIso h.symm⟩

/-- Transfer preservation of limits along an equivalence in the shape. -/
@[to_dual /-- Transfer preservation of colimits along an equivalence in the shape. -/]
lemma preservesLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  preservesLimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cone.ext (Iso.refl _) fun j => ?_
        simp [equ, ← Functor.map_comp]⟩ }

/-- A functor preserving larger limits also preserves smaller limits. -/
@[to_dual /-- A functor preserving larger colimits also preserves smaller colimits. -/]
lemma preservesLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F where
  preservesLimitsOfShape {J} := preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/-- `PreservesLimitsOfSize_shrink.{w, w'} F` tries to obtain `PreservesLimitsOfSize.{w, w'} F`
from some other `PreservesLimitsOfSize F`.
-/
@[to_dual
/-- `PreservesColimitsOfSize_shrink.{w, w'} F` tries to obtain `PreservesColimitsOfSize.{w, w'} F`
from some other `PreservesColimitsOfSize F`.
-/]
lemma preservesLimitsOfSize_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F := preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Preserving limits at any universe level implies preserving limits in universe `0`. -/
@[to_dual /-- Preserving colimits at any universe implies preserving colimits at universe `0`. -/]
lemma preservesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSize_shrink F

/-- A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cone K} (hc : IsLimit (F.mapCone c)) : Nonempty (IsLimit c)

/-- A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[to_dual]
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cocone K} (hc : IsColimit (F.mapCocone c)) : Nonempty (IsColimit c)

/-- A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsLimit : ∀ {K : J ⥤ C}, ReflectsLimit K F := by infer_instance

/-- A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[to_dual]
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[univ_out_params, pp_with_univ]
class ReflectsLimitsOfSize (F : C ⥤ D) : Prop where
  reflectsLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[univ_out_params, pp_with_univ, to_dual]
class ReflectsColimitsOfSize (F : C ⥤ D) : Prop where
  reflectsColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    infer_instance

/-- A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[to_dual
/-- A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/]
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F

/-- A convenience function for `ReflectsLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
@[no_expose, to_dual
/-- A convenience function for `ReflectsColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/]
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c))
    [ReflectsLimit K F] : IsLimit c :=
  (ReflectsLimit.reflects t).some

@[to_dual]
instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

@[to_dual]
instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

@[to_dual]
instance reflects_limits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) reflectsLimit_of_reflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) reflectsLimitsOfShape_of_reflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape

@[to_dual]
instance id_reflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  reflectsLimitsOfShape {J} 𝒥 :=
    { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

@[to_dual]
instance comp_reflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩

@[to_dual]
instance comp_reflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where

@[to_dual]
instance comp_reflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
@[to_dual
/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/]
lemma preservesLimit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`,
then `F` preserves limits of shape `J`.
-/
@[to_dual
/--
If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`,
then `F` preserves colimits of shape `J`.
-/]
lemma preservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := preservesLimit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
@[to_dual
/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/]
lemma preservesLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where
  preservesLimitsOfShape := preservesLimitsOfShape_of_reflects_of_preserves F G

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
@[to_dual /-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/]
lemma reflectsLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F where
  reflects {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoLimit _
    exact Cone.ext (Iso.refl _)⟩

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
@[to_dual /-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/]
lemma reflectsLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where
  reflects t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
@[to_dual
/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/]
lemma reflectsLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  reflectsLimit {K} := reflectsLimit_of_natIso K h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
@[to_dual /-- Transfer reflection of colimits along a natural isomorphism in the functor. -/]
lemma reflectsLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_natIso h

/-- Transfer reflection of limits along an equivalence in the shape. -/
@[to_dual /-- Transfer reflection of colimits along an equivalence in the shape. -/]
lemma reflectsLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where
  reflectsLimit {K} :=
    { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

/-- A functor reflecting larger limits also reflects smaller limits. -/
@[to_dual /-- A functor reflecting larger colimits also reflects smaller colimits. -/]
lemma reflectsLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where
  reflectsLimitsOfShape {J} := reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/-- `reflectsLimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsLimitsOfSize.{w w'} F`
from some other `reflectsLimitsOfSize F`.
-/
@[to_dual
/-- `reflectsColimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsColimitsOfSize.{w w'} F`
from some other `reflectsColimitsOfSize F`.
-/]
lemma reflectsLimitsOfSize_shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F := reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Reflecting limits at any universe implies reflecting limits at universe `0`. -/
@[to_dual]
lemma reflectsSmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSize_shrink F

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsColimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/
@[to_dual
/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsLimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/]
-- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
lemma reflectsLimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where
  reflects {c} t := by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cone.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cone.forget F).map_isIso _
    suffices IsIso ((Cone.functoriality F G).map
      (IsLimit.liftConeMorphism (limit.isLimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cone.functoriality F G)
    exact t.hom_isIso (isLimitOfPreserves G (limit.isLimit F)) _

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
@[to_dual
/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/]
lemma reflectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  reflectsLimit {F} := reflectsLimit_of_reflectsIsomorphisms F G

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
@[to_dual
/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/]
lemma reflectsLimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_reflectsIsomorphisms

end

section

open CategoryTheory.Functor

lemma isIso_app_coconePt_of_preservesColimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J] (K : J ⥤ C) {L L' : C ⥤ D}
    (α : L ⟶ L') [IsIso (whiskerLeft K α)] (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K L] [PreservesColimit K L'] :
    IsIso (α.app c.pt) := by
  let e := IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves L hc) (isColimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  convert! (inferInstance : IsIso e.hom)
  apply (isColimitOfPreserves L hc).hom_ext fun j ↦ ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.mapCocone_ι_app,
    NatTrans.naturality, IsColimit.coconePointsIsoOfNatIso_hom, asIso_hom, e]
  refine (((isColimitOfPreserves L hc).ι_map (L'.mapCocone c) (whiskerLeft K α) j).trans ?_).symm
  simp

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
@[to_dual /-- A fully faithful functor reflects colimits. -/]
instance fullyFaithful_reflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {J} 𝒥₁ :=
    { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cone.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cone.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cone_morphism⟩ } }

end CategoryTheory.Limits
