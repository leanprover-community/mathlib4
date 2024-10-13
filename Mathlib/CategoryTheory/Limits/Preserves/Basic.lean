/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.HasLimits

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


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [CategoryTheory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- A functor `F` preserves limits of `K` (written as `PreservesLimit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cone K}, IsLimit c → IsLimit (F.mapCone c)

/-- A functor `F` preserves colimits of `K` (written as `PreservesColimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cocone K}, IsColimit c → IsColimit (F.mapCocone c)

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesLimitsOfSize.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[Category.{v} J]`. -/
@[nolint checkUnivs, pp_with_univ]
class PreservesLimitsOfSize (F : C ⥤ D) where
  preservesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    infer_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- `PreservesColimitsOfSize.{v u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[Category.{v} J]`. -/
@[nolint checkUnivs, pp_with_univ]
class PreservesColimitsOfSize (F : C ⥤ D) where
  preservesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    infer_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesColimits (F : C ⥤ D) :=
  PreservesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance 100]
  PreservesLimitsOfShape.preservesLimit PreservesLimitsOfSize.preservesLimitsOfShape
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

-- see Note [lower instance priority]
/-- A convenience function for `PreservesLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  PreservesLimit.preserves t

/--
A convenience function for `PreservesColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  PreservesColimit.preserves t

instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance preserves_limits_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance preserves_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance idPreservesLimits : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

instance idPreservesColimits : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  preservesColimitsOfShape {J} 𝒥 :=
    {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

instance [HasLimit K] {F : C ⥤ D} [PreservesLimit K F] : HasLimit (K ⋙ F) where
  exists_limit := ⟨⟨F.mapCone (limit.cone K), PreservesLimit.preserves (limit.isLimit K)⟩⟩

instance [HasColimit K] {F : C ⥤ D} [PreservesColimit K F] : HasColimit (K ⋙ F) where
  exists_colimit :=
    ⟨⟨F.mapCocone (colimit.cocone K), PreservesColimit.preserves (colimit.isColimit K)⟩⟩

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

-- Porting note: made this global by removing local
attribute [elab_without_expected_type] PreservesLimit.preserves PreservesColimit.preserves

instance compPreservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) :=
  ⟨fun h => PreservesLimit.preserves (PreservesLimit.preserves h)⟩

instance compPreservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where

instance compPreservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where

instance compPreservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) :=
  ⟨fun h => PreservesColimit.preserves (PreservesColimit.preserves h)⟩

instance compPreservesColimitsOfShape [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J (F ⋙ G) where

instance compPreservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} (F ⋙ G) where

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preservesLimitOfPreservesLimitCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F :=
  ⟨fun h' => IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
def preservesLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] :
    PreservesLimit K₂ F where
  preserves {c} t := by
    apply IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cones.ext (Iso.refl _)

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
def preservesLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where
  preserves t := IsLimit.mapConeEquiv h (PreservesLimit.preserves t)

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
def preservesLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := preservesLimitOfNatIso K h

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
def preservesLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  preservesLimitsOfShape {_J} _𝒥₁ := preservesLimitsOfShapeOfNatIso h

/-- Transfer preservation of limits along an equivalence in the shape. -/
def preservesLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  preservesLimit {K} :=
    { preserves := fun {c} t => by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cones.ext (Iso.refl _) fun j => ?_
        dsimp
        simp [equ, ← Functor.map_comp] }

/-- A functor preserving larger limits also preserves smaller limits. -/
def preservesLimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F where
  preservesLimitsOfShape {J} := preservesLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

-- See library note [dsimp, simp].
/-- `PreservesLimitsOfSizeShrink.{w w'} F` tries to obtain `PreservesLimitsOfSize.{w w'} F`
from some other `PreservesLimitsOfSize F`.
-/
def preservesLimitsOfSizeShrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F := preservesLimitsOfSizeOfUnivLE.{max w w₂, max w' w₂'} F

/-- Preserving limits at any universe level implies preserving limits in universe `0`. -/
def preservesSmallestLimitsOfPreservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSizeShrink F

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preservesColimitOfPreservesColimitCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun h' => IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preservesColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F] :
    PreservesColimit K₂ F where
  preserves {c} t := by
    apply IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocones.ext (Iso.refl _)

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
def preservesColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G where
  preserves t := IsColimit.mapCoconeEquiv h (PreservesColimit.preserves t)

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
def preservesColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := preservesColimitOfNatIso K h

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
def preservesColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G where
  preservesColimitsOfShape {_J} _𝒥₁ := preservesColimitsOfShapeOfNatIso h

/-- Transfer preservation of colimits along an equivalence in the shape. -/
def preservesColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F where
  preservesColimit {K} :=
    {
      preserves := fun {c} t => by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocones.ext (Iso.refl _) fun j => ?_
        dsimp
        simp [equ, ← Functor.map_comp] }

/-- A functor preserving larger colimits also preserves smaller colimits. -/
def preservesColimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} F where
  preservesColimitsOfShape {J} := preservesColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

-- See library note [dsimp, simp].
/--
`PreservesColimitsOfSizeShrink.{w w'} F` tries to obtain `PreservesColimitsOfSize.{w w'} F`
from some other `PreservesColimitsOfSize F`.
-/
def preservesColimitsOfSizeShrink (F : C ⥤ D) [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F := preservesColimitsOfSizeOfUnivLE.{max w w₂, max w' w₂'} F

/-- Preserving colimits at any universe implies preserving colimits at universe `0`. -/
def preservesSmallestColimitsOfPreservesColimits (F : C ⥤ D) [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSizeShrink F

/-- A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cone K}, IsLimit (F.mapCone c) → IsLimit c

/-- A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cocone K}, IsColimit (F.mapCocone c) → IsColimit c

/-- A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  reflectsLimit : ∀ {K : J ⥤ C}, ReflectsLimit K F := by infer_instance

/-- A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  reflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[nolint checkUnivs, pp_with_univ]
class ReflectsLimitsOfSize (F : C ⥤ D) where
  reflectsLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    infer_instance

/-- A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[nolint checkUnivs, pp_with_univ]
class ReflectsColimitsOfSize (F : C ⥤ D) where
  reflectsColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    infer_instance

/-- A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
abbrev ReflectsColimits (F : C ⥤ D) :=
  ReflectsColimitsOfSize.{v₂, v₂} F

/-- A convenience function for `ReflectsLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c))
    [ReflectsLimit K F] : IsLimit c := ReflectsLimit.reflects t

/--
A convenience function for `ReflectsColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
    [ReflectsColimit K F] : IsColimit c :=
  ReflectsColimit.reflects t

instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance
  reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance
  reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

instance reflects_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!; subsingleton

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitOfReflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitOfReflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  ReflectsColimitsOfShape.reflectsColimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitsOfShapeOfReflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitsOfShapeOfReflectsColimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  ReflectsColimitsOfSize.reflectsColimitsOfShape

instance idReflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  reflectsLimitsOfShape {J} 𝒥 :=
    {
      reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

instance idReflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  reflectsColimitsOfShape {J} 𝒥 :=
    {
      reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

instance compReflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun h => ReflectsLimit.reflects (ReflectsLimit.reflects h)⟩

instance compReflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where

instance compReflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where

instance compReflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) :=
  ⟨fun h => ReflectsColimit.reflects (ReflectsColimit.reflects h)⟩

instance compReflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) where

instance compReflectsColimits [ReflectsColimitsOfSize.{w', w} F]
    [ReflectsColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} (F ⋙ G) where

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
def preservesLimitOfReflectsOfPreserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun h => by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
def preservesLimitsOfShapeOfReflectsOfPreserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := preservesLimitOfReflectsOfPreserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
def preservesLimitsOfReflectsOfPreserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where
  preservesLimitsOfShape := preservesLimitsOfShapeOfReflectsOfPreserves F G

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
def reflectsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F where
  reflects {c} t := by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) _).symm t).ofIsoLimit _
    exact Cones.ext (Iso.refl _)

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
def reflectsLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where
  reflects t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
def reflectsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  reflectsLimit {K} := reflectsLimitOfNatIso K h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
def reflectsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShapeOfNatIso h

/-- Transfer reflection of limits along an equivalence in the shape. -/
def reflectsLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where
  reflectsLimit {K} :=
    {
      reflects := fun {c} t => by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _ }

/-- A functor reflecting larger limits also reflects smaller limits. -/
def reflectsLimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where
  reflectsLimitsOfShape {J} := reflectsLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

/-- `reflectsLimitsOfSizeShrink.{w w'} F` tries to obtain `reflectsLimitsOfSize.{w w'} F`
from some other `reflectsLimitsOfSize F`.
-/
def reflectsLimitsOfSizeShrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F := reflectsLimitsOfSizeOfUnivLE.{max w w₂, max w' w₂'} F

/-- Reflecting limits at any universe implies reflecting limits at universe `0`. -/
def reflectsSmallestLimitsOfReflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSizeShrink F

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
def reflectsLimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where
  reflects {c} t := by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from by
      apply IsLimit.ofPointIso (limit.isLimit F)
    change IsIso ((Cones.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cones.forget F).map_isIso _
    suffices IsIso (Prefunctor.map (Cones.functoriality F G).toPrefunctor
      (IsLimit.liftConeMorphism (limit.isLimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cones.functoriality F G)
    exact t.hom_isIso (isLimitOfPreserves G (limit.isLimit F)) _

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
def reflectsLimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  reflectsLimit {F} := reflectsLimitOfReflectsIsomorphisms F G

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
def reflectsLimitsOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShapeOfReflectsIsomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
def preservesColimitOfReflectsOfPreserves [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun {c} h => by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩

/-- If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
def preservesColimitsOfShapeOfReflectsOfPreserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit := preservesColimitOfReflectsOfPreserves F G

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
def preservesColimitsOfReflectsOfPreserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F where
  preservesColimitsOfShape := preservesColimitsOfShapeOfReflectsOfPreserves F G

/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
def reflectsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F where
  reflects {c} t := by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) _).symm t).ofIsoColimit _
    exact Cocones.ext (Iso.refl _)

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
def reflectsColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G where
  reflects t := ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
def reflectsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where
  reflectsColimit {K} := reflectsColimitOfNatIso K h

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
def reflectsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G where
  reflectsColimitsOfShape := reflectsColimitsOfShapeOfNatIso h

/-- Transfer reflection of colimits along an equivalence in the shape. -/
def reflectsColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F where
  reflectsColimit :=
    {
      reflects := fun {c} t => by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _ }

/-- A functor reflecting larger colimits also reflects smaller colimits. -/
def reflectsColimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F where
  reflectsColimitsOfShape {J} := reflectsColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

/-- `reflectsColimitsOfSizeShrink.{w w'} F` tries to obtain `reflectsColimitsOfSize.{w w'} F`
from some other `reflectsColimitsOfSize F`.
-/
def reflectsColimitsOfSizeShrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F := reflectsColimitsOfSizeOfUnivLE.{max w w₂, max w' w₂'} F

/-- Reflecting colimits at any universe implies reflecting colimits at universe `0`. -/
def reflectsSmallestColimitsOfReflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsColimitsOfSizeShrink F

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
def reflectsColimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G where
  reflects {c} t := by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from by
      apply IsColimit.ofPointIso (colimit.isColimit F)
    change IsIso ((Cocones.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
      apply (Cocones.forget F).map_isIso _
    suffices IsIso (Prefunctor.map (Cocones.functoriality F G).toPrefunctor
      (IsColimit.descCoconeMorphism (colimit.isColimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cocones.functoriality F G)
    exact (isColimitOfPreserves G (colimit.isColimit F)).hom_isIso t _

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
def reflectsColimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G where
  reflectsColimit {F} := reflectsColimitOfReflectsIsomorphisms F G

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
def reflectsColimitsOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G where
  reflectsColimitsOfShape := reflectsColimitsOfShapeOfReflectsIsomorphisms

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
instance fullyFaithfulReflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {J} 𝒥₁ :=
    { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            (IsLimit.mkConeMorphism fun s =>
                (Cones.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cones.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cone_morphism } }

/-- A fully faithful functor reflects colimits. -/
instance fullyFaithfulReflectsColimits [F.Full] [F.Faithful] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {J} 𝒥₁ :=
    { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            (IsColimit.mkCoconeMorphism fun s =>
                (Cocones.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocones.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cocone_morphism }}

end CategoryTheory.Limits
