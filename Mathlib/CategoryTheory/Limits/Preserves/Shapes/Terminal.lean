/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.shapes.terminal from "leanprover-community/mathlib"@"bbe25d4d92565a5fd773e52e041a90387eee3c93"

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminalComparison G` is an isomorphism iff `G` preserves terminal
objects.
-/


universe w v v₁ v₂ u u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable (X : C)

section Terminal

/-- The map of an empty cone is a limit iff the mapped object is terminal.
-/
def isLimitMapConeEmptyConeEquiv :
    IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)
#align category_theory.limits.is_limit_map_cone_empty_cone_equiv CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv

/-- The property of preserving terminal objects expressed in terms of `IsTerminal`. -/
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (PreservesLimit.preserves l)
#align category_theory.limits.is_terminal.is_terminal_obj CategoryTheory.Limits.IsTerminal.isTerminalObj

/-- The property of reflecting terminal objects expressed in terms of `IsTerminal`. -/
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  ReflectsLimit.reflects ((isLimitMapConeEmptyConeEquiv G X).symm l)
#align category_theory.limits.is_terminal.is_terminal_of_obj CategoryTheory.Limits.IsTerminal.isTerminalOfObj

/-- Preserving the terminal object implies preserving all limits of the empty diagram. -/
def preservesLimitsOfShapePemptyOfPreservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty) G
    where preservesLimit :=
    preservesLimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)
#align category_theory.limits.preserves_limits_of_shape_pempty_of_preserves_terminal CategoryTheory.Limits.preservesLimitsOfShapePemptyOfPreservesTerminal

variable [HasTerminal C]

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)
#align category_theory.limits.is_limit_of_has_terminal_of_preserves_limit CategoryTheory.Limits.isLimitOfHasTerminalOfPreservesLimit

/-- If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  haveI := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  -- ⊢ HasLimit F
  apply hasLimitOfIso F.uniqueFromEmpty.symm⟩
  -- 🎉 no goals
#align category_theory.limits.has_terminal_of_has_terminal_of_preserves_limit CategoryTheory.Limits.hasTerminal_of_hasTerminal_of_preservesLimit

variable [HasTerminal D]

/-- If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def PreservesTerminal.ofIsoComparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty C) G := by
  apply preservesLimitOfPreservesLimitCone terminalIsTerminal
  -- ⊢ IsLimit (G.mapCone (asEmptyCone (⊤_ C)))
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  -- ⊢ IsTerminal (G.obj (⊤_ C))
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i
  -- 🎉 no goals
#align category_theory.limits.preserves_terminal.of_iso_comparison CategoryTheory.Limits.PreservesTerminal.ofIsoComparison

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIsIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  -- ⊢ PreservesLimit (Functor.empty C) G
  exact PreservesTerminal.ofIsoComparison G
  -- 🎉 no goals
#align category_theory.limits.preserves_terminal_of_is_iso CategoryTheory.Limits.preservesTerminalOfIsIso

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty C) G :=
  preservesTerminalOfIsIso G f.hom
#align category_theory.limits.preserves_terminal_of_iso CategoryTheory.Limits.preservesTerminalOfIso

variable [PreservesLimit (Functor.empty.{0} C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)
#align category_theory.limits.preserves_terminal.iso CategoryTheory.Limits.PreservesTerminal.iso

@[simp]
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).hom = terminalComparison G :=
  rfl
#align category_theory.limits.preserves_terminal.iso_hom CategoryTheory.Limits.PreservesTerminal.iso_hom

instance : IsIso (terminalComparison G) := by
  rw [← PreservesTerminal.iso_hom]
  -- ⊢ IsIso (PreservesTerminal.iso G).hom
  infer_instance
  -- 🎉 no goals

end Terminal

section Initial

/-- The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def isColimitMapCoconeEmptyCoconeEquiv :
    IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)
#align category_theory.limits.is_colimit_map_cocone_empty_cocone_equiv CategoryTheory.Limits.isColimitMapCoconeEmptyCoconeEquiv

/-- The property of preserving initial objects expressed in terms of `IsInitial`. -/
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) :
    IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (PreservesColimit.preserves l)
#align category_theory.limits.is_initial.is_initial_obj CategoryTheory.Limits.IsInitial.isInitialObj

/-- The property of reflecting initial objects expressed in terms of `IsInitial`. -/
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) :
    IsInitial X :=
  ReflectsColimit.reflects ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)
#align category_theory.limits.is_initial.is_initial_of_obj CategoryTheory.Limits.IsInitial.isInitialOfObj

/-- Preserving the initial object implies preserving all colimits of the empty diagram. -/
def preservesColimitsOfShapePemptyOfPreservesInitial [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete PEmpty) G
    where preservesColimit :=
    preservesColimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)
#align category_theory.limits.preserves_colimits_of_shape_pempty_of_preserves_initial CategoryTheory.Limits.preservesColimitsOfShapePemptyOfPreservesInitial

variable [HasInitial C]

/-- If `G` preserves the initial object and `C` has an initial object, then the image of the initial
object is initial.
-/
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)
#align category_theory.limits.is_colimit_of_has_initial_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasInitialOfPreservesColimit

/-- If `C` has an initial object and `G` preserves initial objects, then `D` has an initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for general `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily have colimits of
shape `J`.
-/
theorem hasInitial_of_hasInitial_of_preservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    HasInitial D :=
  ⟨fun F => by
    haveI := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    -- ⊢ HasColimit F
    apply hasColimitOfIso F.uniqueFromEmpty⟩
    -- 🎉 no goals
#align category_theory.limits.has_initial_of_has_initial_of_preserves_colimit CategoryTheory.Limits.hasInitial_of_hasInitial_of_preservesColimit

variable [HasInitial D]

/-- If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
def PreservesInitial.ofIsoComparison [i : IsIso (initialComparison G)] :
    PreservesColimit (Functor.empty C) G := by
  apply preservesColimitOfPreservesColimitCocone initialIsInitial
  -- ⊢ IsColimit (G.mapCocone (asEmptyCocone (⊥_ C)))
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  -- ⊢ IsInitial (G.obj (⊥_ C))
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i
  -- 🎉 no goals
#align category_theory.limits.preserves_initial.of_iso_comparison CategoryTheory.Limits.PreservesInitial.ofIsoComparison

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
def preservesInitialOfIsIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] :
    PreservesColimit (Functor.empty C) G := by
  rw [Subsingleton.elim f (initialComparison G)] at i
  -- ⊢ PreservesColimit (Functor.empty C) G
  exact PreservesInitial.ofIsoComparison G
  -- 🎉 no goals
#align category_theory.limits.preserves_initial_of_is_iso CategoryTheory.Limits.preservesInitialOfIsIso

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥ `, then `G` preserves initial objects. -/
def preservesInitialOfIso (f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Functor.empty C) G :=
  preservesInitialOfIsIso G f.hom
#align category_theory.limits.preserves_initial_of_iso CategoryTheory.Limits.preservesInitialOfIso

variable [PreservesColimit (Functor.empty.{0} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)
#align category_theory.limits.preserves_initial.iso CategoryTheory.Limits.PreservesInitial.iso

@[simp]
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl
#align category_theory.limits.preserves_initial.iso_hom CategoryTheory.Limits.PreservesInitial.iso_hom

instance : IsIso (initialComparison G) := by
  rw [← PreservesInitial.iso_hom]
  -- ⊢ IsIso (PreservesInitial.iso G).inv
  infer_instance
  -- 🎉 no goals

end Initial

end CategoryTheory.Limits
