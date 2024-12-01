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
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cone K} (hc : IsLimit c) : Nonempty (IsLimit (F.mapCone c))

/-- A functor `F` preserves colimits of `K` (written as `PreservesColimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cocone K} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c))

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesLimitsOfSize.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[Category.{v} J]`. -/
@[nolint checkUnivs, pp_with_univ]
class PreservesLimitsOfSize (F : C ⥤ D) : Prop where
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
class PreservesColimitsOfSize (F : C ⥤ D) : Prop where
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
  (PreservesLimit.preserves t).some

/--
A convenience function for `PreservesColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  (PreservesColimit.preserves t).some

instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance preservesLimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance preservesColimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance id_preservesLimitsOfSize : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

@[deprecated "use id_preservesLimitsOfSize" (since := "2024-11-19")]
lemma idPreservesLimits : PreservesLimitsOfSize.{w', w} (𝟭 C) :=
  id_preservesLimitsOfSize

instance id_preservesColimitsOfSize : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  preservesColimitsOfShape {J} 𝒥 :=
    {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

@[deprecated "use id_preservesColimitsOfSize" (since := "2024-11-19")]
lemma idPreservesColimits : PreservesColimitsOfSize.{w', w} (𝟭 C) :=
  id_preservesColimitsOfSize

instance [HasLimit K] {F : C ⥤ D} [PreservesLimit K F] : HasLimit (K ⋙ F) where
  exists_limit := ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩

instance [HasColimit K] {F : C ⥤ D} [PreservesColimit K F] : HasColimit (K ⋙ F) where
  exists_colimit := ⟨_, isColimitOfPreserves F (colimit.isColimit K)⟩

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

-- Porting note: made this global by removing local
attribute [elab_without_expected_type] PreservesLimit.preserves PreservesColimit.preserves

instance comp_preservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) where
  preserves hc := ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩

instance comp_preservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where

instance comp_preservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where

instance comp_preservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) where
  preserves hc := ⟨isColimitOfPreserves G (isColimitOfPreserves F hc)⟩

instance comp_preservesColimitsOfShape [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J (F ⋙ G) where

instance comp_preservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} (F ⋙ G) where

@[deprecated "use comp_preservesLimit" (since := "2024-11-19")]
lemma compPreservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) := inferInstance

@[deprecated "use comp_preservesLimitsOfShape" (since := "2024-11-19")]
lemma compPreservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) :=
  comp_preservesLimitsOfShape _ _

@[deprecated "use comp_preservesLimits" (since := "2024-11-19")]
lemma compPreservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) :=
  comp_preservesLimits _ _

@[deprecated "use comp_preservesColimit" (since := "2024-11-19")]
lemma compPreservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) := inferInstance

@[deprecated "use comp_preservesColimitsOfShape" (since := "2024-11-19")]
lemma compPreservesColimitsOfShape [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (F ⋙ G) :=
  comp_preservesColimitsOfShape _ _

@[deprecated "use comp_preservesColimits" (since := "2024-11-19")]
lemma compPreservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] :
    PreservesColimitsOfSize.{w', w} (F ⋙ G) :=
  comp_preservesColimits _ _

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
lemma preservesLimit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F where
  preserves h' := ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

@[deprecated "use preservesLimit_of_preserves_limit_cone" (since := "2024-11-19")]
lemma preservesLimitOfPreservesLimitCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F :=
preservesLimit_of_preserves_limit_cone h hF

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
lemma preservesLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesLimit K₁ F] : PreservesLimit K₂ F where
  preserves {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cones.ext (Iso.refl _)⟩

@[deprecated "use preservesLimit_of_iso_diagram" (since := "2024-11-19")]
lemma preservesLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesLimit K₁ F] : PreservesLimit K₂ F :=
  preservesLimit_of_iso_diagram F h

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
lemma preservesLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where
  preserves t := ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩

@[deprecated "use preservesLimit_of_natIso" (since := "2024-11-19")]
lemma preservesLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G :=
  preservesLimit_of_natIso K h

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
lemma preservesLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := preservesLimit_of_natIso K h

@[deprecated "use preservesLimitsOfShape_of_natIso" (since := "2024-11-19")]
lemma preservesLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G :=
  preservesLimitsOfShape_of_natIso h

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
lemma preservesLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  preservesLimitsOfShape := preservesLimitsOfShape_of_natIso h

@[deprecated "use preservesLimits_of_natIso" (since := "2024-11-19")]
lemma preservesLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G :=
  preservesLimits_of_natIso h

/-- Transfer preservation of limits along an equivalence in the shape. -/
lemma preservesLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  preservesLimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cones.ext (Iso.refl _) fun j => ?_
        dsimp
        simp [equ, ← Functor.map_comp]⟩ }

@[deprecated "use preservesLimitsOfShape_of_equiv" (since := "2024-11-19")]
lemma preservesLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F :=
  preservesLimitsOfShape_of_equiv e F

/-- A functor preserving larger limits also preserves smaller limits. -/
lemma preservesLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F where
  preservesLimitsOfShape {J} := preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

@[deprecated "use preservesLimitsOfSize_of_univLE" (since := "2024-11-19")]
lemma preservesLimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F :=
  preservesLimitsOfSize_of_univLE.{w', w₂'} F

-- See library note [dsimp, simp].
/-- `PreservesLimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesLimitsOfSize.{w w'} F`
from some other `PreservesLimitsOfSize F`.
-/
lemma preservesLimitsOfSize_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F := preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

@[deprecated "use preservesLimitsOfSize_shrink" (since := "2024-11-19")]
lemma PreservesLimitsOfSizeShrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F :=
  preservesLimitsOfSize_shrink F

/-- Preserving limits at any universe level implies preserving limits in universe `0`. -/
lemma preservesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSize_shrink F

@[deprecated "use preservesSmallestLimits_of_preservesLimits" (since := "2024-11-19")]
lemma preservesSmallestLimitsOfPreservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesSmallestLimits_of_preservesLimits F

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
lemma preservesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun h' => ⟨IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩⟩

@[deprecated "use preservesColimit_of_preserves_colimit_cocone" (since := "2024-11-19")]
lemma preservesColimitOfPreservesColimitCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
preservesColimit_of_preserves_colimit_cocone h hF

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
lemma preservesColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesColimit K₁ F] :
    PreservesColimit K₂ F where
  preserves {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocones.ext (Iso.refl _)⟩

@[deprecated "use preservesColimit_of_iso_diagram" (since := "2024-11-19")]
lemma preservesColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesColimit K₁ F] :
    PreservesColimit K₂ F :=
  preservesColimit_of_iso_diagram F h

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
lemma preservesColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G where
  preserves t := ⟨IsColimit.mapCoconeEquiv h (isColimitOfPreserves F t)⟩

@[deprecated preservesColimit_of_natIso (since := "2024-11-19")]
lemma preservesColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G :=
  preservesColimit_of_natIso K h

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
lemma preservesColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := preservesColimit_of_natIso K h

@[deprecated "use preservesColimitsOfShape_of_natIso" (since := "2024-11-19")]
lemma preservesColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G :=
  preservesColimitsOfShape_of_natIso h

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
lemma preservesColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G where
  preservesColimitsOfShape {_J} _𝒥₁ := preservesColimitsOfShape_of_natIso h

@[deprecated "use preservesColimits_of_natIso" (since := "2024-11-19")]
lemma preservesColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G :=
  preservesColimits_of_natIso h

/-- Transfer preservation of colimits along an equivalence in the shape. -/
lemma preservesColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F where
  preservesColimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocones.ext (Iso.refl _) fun j => ?_
        dsimp
        simp [equ, ← Functor.map_comp]⟩ }

@[deprecated "use preservesColimitsOfShape_of_equiv" (since := "2024-11-19")]
lemma preservesColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F :=
  preservesColimitsOfShape_of_equiv e F

/-- A functor preserving larger colimits also preserves smaller colimits. -/
lemma preservesColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} F where
  preservesColimitsOfShape {J} := preservesColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

@[deprecated "use preservesColimitsOfSize_of_univLE" (since := "2024-11-19")]
lemma preservesColimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} F :=
  preservesColimitsOfSize_of_univLE.{w', w₂'} F

-- See library note [dsimp, simp].
/--
`PreservesColimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesColimitsOfSize.{w w'} F`
from some other `PreservesColimitsOfSize F`.
-/
lemma preservesColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F := preservesColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

@[deprecated "use preservesColimitsOfSize_shrink" (since := "2024-11-19")]
lemma PreservesColimitsOfSizeShrink (F : C ⥤ D)
    [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F :=
  preservesColimitsOfSize_shrink F

/-- Preserving colimits at any universe implies preserving colimits at universe `0`. -/
lemma preservesSmallestColimits_of_preservesColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSize_shrink F

@[deprecated "use preservesSmallestColimits_of_preservesColimits" (since := "2024-11-19")]
lemma preservesSmallestColimitsOfPreservesColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesSmallestColimits_of_preservesColimits F

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
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[nolint checkUnivs, pp_with_univ]
class ReflectsLimitsOfSize (F : C ⥤ D) : Prop where
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
class ReflectsColimitsOfSize (F : C ⥤ D) : Prop where
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
    [ReflectsLimit K F] : IsLimit c :=
  (ReflectsLimit.reflects t).some

/--
A convenience function for `ReflectsColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
    [ReflectsColimit K F] : IsColimit c :=
  (ReflectsColimit.reflects t).some

instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance
  reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance
  reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

instance reflects_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimit_of_reflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimit_of_reflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  ReflectsColimitsOfShape.reflectsColimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitsOfShape_of_reflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitsOfShape_of_reflectsColimits
    (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  ReflectsColimitsOfSize.reflectsColimitsOfShape

instance id_reflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  reflectsLimitsOfShape {J} 𝒥 :=
    { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

@[deprecated "use id_reflectsLimits" (since := "2024-11-19")]
lemma idReflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) := id_reflectsLimits

instance id_reflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  reflectsColimitsOfShape {J} 𝒥 :=
    { reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

@[deprecated "use id_reflectsColimits" (since := "2024-11-19")]
lemma idReflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) := id_reflectsColimits

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

instance comp_reflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩

instance comp_reflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where

instance comp_reflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where

instance comp_reflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) :=
  ⟨fun h => ReflectsColimit.reflects (isColimitOfReflects G h)⟩

instance comp_reflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) where

instance comp_reflectsColimits [ReflectsColimitsOfSize.{w', w} F]
    [ReflectsColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} (F ⋙ G) where

@[deprecated "use comp_reflectsLimit" (since := "2024-11-19")]
lemma compReflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) := inferInstance

@[deprecated "use comp_reflectsLimitsOfShape " (since := "2024-11-19")]
lemma compReflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) := inferInstance

@[deprecated "use comp_reflectsLimits" (since := "2024-11-19")]
lemma compReflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) := inferInstance

@[deprecated "use comp_reflectsColimit" (since := "2024-11-19")]
lemma compReflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) := inferInstance

@[deprecated "use comp_reflectsColimitsOfShape " (since := "2024-11-19")]
lemma compReflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) := inferInstance

@[deprecated "use comp_reflectsColimits" (since := "2024-11-19")]
lemma compReflectsColimits [ReflectsColimitsOfSize.{w', w} F] [ReflectsColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} (F ⋙ G) := inferInstance

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
lemma preservesLimit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

@[deprecated "use preservesLimit_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesLimitOfReflectsOfPreserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  preservesLimit_of_reflects_of_preserves F G

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
lemma preservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := preservesLimit_of_reflects_of_preserves F G

@[deprecated "use preservesLimitsOfShape_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesLimitsOfShapeOfReflectsOfPreserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F :=
  preservesLimitsOfShape_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
lemma preservesLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where
  preservesLimitsOfShape := preservesLimitsOfShape_of_reflects_of_preserves F G

@[deprecated "use preservesLimits_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesLimitsOfReflectsOfPreserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F :=
  preservesLimits_of_reflects_of_preserves.{w', w} F G

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
lemma reflectsLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F where
  reflects {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) _).symm t).ofIsoLimit _
    exact Cones.ext (Iso.refl _)⟩

@[deprecated "use reflectsLimit_of_iso_diagram" (since := "2024-11-19")]
lemma reflectsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F :=
  reflectsLimit_of_iso_diagram F h

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
lemma reflectsLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where
  reflects t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

@[deprecated "use reflectsLimit_of_natIso" (since := "2024-11-19")]
lemma reflectsLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G :=
  reflectsLimit_of_natIso K h

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
lemma reflectsLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  reflectsLimit {K} := reflectsLimit_of_natIso K h

@[deprecated "use reflectsLimitsOfShape_of_natIso" (since := "2024-11-19")]
lemma reflectsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G :=
  reflectsLimitsOfShape_of_natIso h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
lemma reflectsLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_natIso h

@[deprecated "use reflectsLimits_of_natIso" (since := "2024-11-19")]
lemma reflectsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G :=
  reflectsLimits_of_natIso h

/-- Transfer reflection of limits along an equivalence in the shape. -/
lemma reflectsLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where
  reflectsLimit {K} :=
    { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

@[deprecated "use reflectsLimitsOfShape_of_equiv" (since := "2024-11-19")]
lemma reflectsLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F :=
  reflectsLimitsOfShape_of_equiv e F

/-- A functor reflecting larger limits also reflects smaller limits. -/
lemma reflectsLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where
  reflectsLimitsOfShape {J} := reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

@[deprecated "use reflectsLimitsOfSize_of_univLE" (since := "2024-11-19")]
lemma reflectsLimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F :=
  reflectsLimitsOfSize_of_univLE.{w'} F

/-- `reflectsLimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsLimitsOfSize.{w w'} F`
from some other `reflectsLimitsOfSize F`.
-/
lemma reflectsLimitsOfSize_shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F := reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

@[deprecated "use reflectsLimitsOfSize_shrink" (since := "2024-11-19")]
lemma reflectsLimitsOfSizeShrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F :=
  reflectsLimitsOfSize_shrink F

/-- Reflecting limits at any universe implies reflecting limits at universe `0`. -/
lemma reflectsSmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSize_shrink F

@[deprecated "use reflectsSmallestLimits_of_reflectsLimits" (since := "2024-11-19")]
lemma reflectsSmallestLimitsOfReflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsSmallestLimits_of_reflectsLimits F

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
lemma reflectsLimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where
  reflects {c} t := by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cones.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cones.forget F).map_isIso _
    suffices IsIso (Prefunctor.map (Cones.functoriality F G).toPrefunctor
      (IsLimit.liftConeMorphism (limit.isLimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cones.functoriality F G)
    exact t.hom_isIso (isLimitOfPreserves G (limit.isLimit F)) _

@[deprecated "use reflectsLimit_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsLimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G :=
  reflectsLimit_of_reflectsIsomorphisms F G

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
lemma reflectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  reflectsLimit {F} := reflectsLimit_of_reflectsIsomorphisms F G

@[deprecated "use reflectsLimitsOfShape_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsLimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
lemma reflectsLimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_reflectsIsomorphisms

@[deprecated "use reflectsLimits_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsLimitsOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G :=
  reflectsLimits_of_reflectsIsomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
lemma preservesColimit_of_reflects_of_preserves
    [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun {c} h => ⟨by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩⟩

@[deprecated "use preservesColimit_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesColimitOfReflectsOfPreserves
    [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  preservesColimit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
lemma preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit := preservesColimit_of_reflects_of_preserves F G

@[deprecated "use preservesColimitsOfShape_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesColimitsOfShapeOfReflectsOfPreserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F :=
  preservesColimitsOfShape_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
lemma preservesColimits_of_reflects_of_preserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflects_of_preserves F G

@[deprecated "use preservesColimits_of_reflects_of_preserves" (since := "2024-11-19")]
lemma preservesColimitsOfReflectsOfPreserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F :=
  preservesColimits_of_reflects_of_preserves F G

/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
lemma reflectsColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F where
  reflects {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) _).symm t).ofIsoColimit _
    exact Cocones.ext (Iso.refl _)⟩

@[deprecated "use reflectsColimit_of_iso_diagram" (since := "2024-11-19")]
lemma reflectsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F :=
  reflectsColimit_of_iso_diagram F h

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
lemma reflectsColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G where
  reflects t := ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

@[deprecated "use reflectsColimit_of_natIso" (since := "2024-11-19")]
lemma reflectsColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G :=
  reflectsColimit_of_natIso K h

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
lemma reflectsColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where
  reflectsColimit {K} := reflectsColimit_of_natIso K h

@[deprecated "use reflectsColimitsOfShape_of_natIso" (since := "2024-11-19")]
lemma reflectsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G :=
  reflectsColimitsOfShape_of_natIso h

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
lemma reflectsColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_natIso h

@[deprecated "use reflectsColimits_of_natIso" (since := "2024-11-19")]
lemma reflectsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G :=
  reflectsColimits_of_natIso h

/-- Transfer reflection of colimits along an equivalence in the shape. -/
lemma reflectsColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F where
  reflectsColimit :=
    { reflects := fun {c} t => ⟨by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _⟩ }

@[deprecated "use reflectsColimitsOfShape_of_equiv" (since := "2024-11-19")]
lemma reflectsColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F :=
  reflectsColimitsOfShape_of_equiv e F

/-- A functor reflecting larger colimits also reflects smaller colimits. -/
lemma reflectsColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F where
  reflectsColimitsOfShape {J} := reflectsColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm F

@[deprecated "use reflectsColimitsOfSize_of_univLE" (since := "2024-11-19")]
lemma reflectsColimitsOfSizeOfUnivLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F :=
  reflectsColimitsOfSize_of_univLE.{w'} F

/-- `reflectsColimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsColimitsOfSize.{w w'} F`
from some other `reflectsColimitsOfSize F`.
-/
lemma reflectsColimitsOfSize_shrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F := reflectsColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

@[deprecated "use reflectsColimitsOfSize_shrink" (since := "2024-11-19")]
lemma reflectsColimitsOfSizeShrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F :=
  reflectsColimitsOfSize_shrink F

/-- Reflecting colimits at any universe implies reflecting colimits at universe `0`. -/
lemma reflectsSmallestColimits_of_reflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsColimitsOfSize_shrink F

@[deprecated "use reflectsSmallestColimits_of_reflectsColimits" (since := "2024-11-19")]
lemma reflectsSmallestColimitsOfReflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsSmallestColimits_of_reflectsColimits F

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
lemma reflectsColimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G where
  reflects {c} t := by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from ⟨by
      apply IsColimit.ofPointIso (colimit.isColimit F)⟩
    change IsIso ((Cocones.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
      apply (Cocones.forget F).map_isIso _
    suffices IsIso (Prefunctor.map (Cocones.functoriality F G).toPrefunctor
      (IsColimit.descCoconeMorphism (colimit.isColimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cocones.functoriality F G)
    exact (isColimitOfPreserves G (colimit.isColimit F)).hom_isIso t _

@[deprecated "use reflectsColimit_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsColimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G :=
  reflectsColimit_of_reflectsIsomorphisms F G

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
lemma reflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G where
  reflectsColimit {F} := reflectsColimit_of_reflectsIsomorphisms F G

@[deprecated "use reflectsColimitsOfShape_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsColimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
lemma reflectsColimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_reflectsIsomorphisms

@[deprecated "use reflectsColimits_of_reflectsIsomorphisms" (since := "2024-11-19")]
lemma reflectsColimitsOfReflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G :=
  reflectsColimits_of_reflectsIsomorphisms

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
instance fullyFaithful_reflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {J} 𝒥₁ :=
    { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cones.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cones.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cone_morphism⟩ } }

@[deprecated "use fullyFaithful_reflectsLimits" (since := "2024-11-19")]
lemma fullyFaithfulReflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F :=
  inferInstance

/-- A fully faithful functor reflects colimits. -/
instance fullyFaithful_reflectsColimits [F.Full] [F.Faithful] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {J} 𝒥₁ :=
    { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsColimit.mkCoconeMorphism fun _ =>
                (Cocones.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocones.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cocone_morphism⟩ }}

@[deprecated "use fullyFaithful_reflectsColimits" (since := "2024-11-19")]
lemma fullyFaithfulReflectsColimits [F.Full] [F.Faithful] : ReflectsColimitsOfSize.{w, w'} F :=
  inferInstance

end CategoryTheory.Limits
