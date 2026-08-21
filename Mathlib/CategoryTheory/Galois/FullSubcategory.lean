/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Full subcategories of Galois categories

Given a Galois category `C`, we introduce a typeclass `P.IsGaloisSubcategory`
which allows to show that `P.FullSubcategory` is also a Galois category.

-/

universe w v u

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

/-- If `P` is a property of objects in a Galois category, the typeclass
`IsGaloisSubcategory` expresses stability properties which imply that
the fullsubcategory given by `P` is also a Galois category. -/
class IsGaloisSubcategory (P : ObjectProperty C) : Prop where
  /-- If `C` has a terminal object,`P` is sat. -/
  isClosedUnderLimitsOfShape_discrete_pEmpty :
    P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := by infer_instance
  /-- `P` is stable under pullbacks. -/
  isClosedUnderLimitsOfShape_walkingCospan :
    P.IsClosedUnderLimitsOfShape WalkingCospan := by infer_instance
  /-- `P` is stable under finite coproducs. -/
  isClosedUnderColimitsOfShape_discrete (ι : Type) [Finite ι] :
    P.IsClosedUnderColimitsOfShape (Discrete ι) := by infer_instance
  /-- `P` is stable under quotients by finite groups. -/
  isClosedUnderColimitsOfShape_singleObj (G : Type v) [Group G] [Finite G] :
    P.IsClosedUnderColimitsOfShape (SingleObj G) := by infer_instance
  isClosedUnderSubobjects : P.IsClosedUnderSubobjects := by infer_instance
  preservesEpimorphisms : P.ι.PreservesEpimorphisms := by infer_instance

namespace IsGaloisSubcategory

attribute [instance] isClosedUnderLimitsOfShape_discrete_pEmpty
  isClosedUnderLimitsOfShape_walkingCospan
  isClosedUnderColimitsOfShape_discrete
  isClosedUnderColimitsOfShape_singleObj
  isClosedUnderSubobjects preservesEpimorphisms

end IsGaloisSubcategory

end ObjectProperty

namespace PreGaloisCategory

instance [PreGaloisCategory C] [MonoCoprod C]
    (P : ObjectProperty C) [P.IsGaloisSubcategory] :
    PreGaloisCategory P.FullSubcategory where
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    have : Mono i.hom := inferInstanceAs (Mono (P.ι.map i))
    obtain ⟨Z, u, ⟨h⟩⟩ := monoInducesIsoOnDirectSummand i.hom
    refine ⟨⟨Z, ?_⟩, ObjectProperty.homMk u,
      ⟨isColimitOfReflects P.ι ((isColimitMapCoconeBinaryCofanEquiv ..).2 h)⟩⟩
    have : Mono u := MonoCoprod.binaryCofan_inr _ h
    exact P.prop_of_mono u Y.property
  hasFiniteCoproducts := ⟨inferInstance⟩
  hasQuotientsByFiniteGroups _ _ := inferInstance

instance [PreGaloisCategory C] [MonoCoprod C]
    (P : ObjectProperty C) [P.IsGaloisSubcategory]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] :
    FiberFunctor (P.ι ⋙ F) where
  preservesFiniteCoproducts := ⟨inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ := inferInstance

end PreGaloisCategory

namespace GaloisCategory

instance [GaloisCategory C] (P : ObjectProperty C) [P.IsGaloisSubcategory] :
    GaloisCategory P.FullSubcategory where
  hasFiberFunctor := by
    obtain ⟨F, _⟩ := hasFiberFunctor (C := C)
    exact ⟨P.ι ⋙ F, inferInstance⟩

end GaloisCategory

end CategoryTheory
