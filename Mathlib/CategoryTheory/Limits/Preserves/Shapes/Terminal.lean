/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Basic

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

/-- The property of preserving terminal objects expressed in terms of `IsTerminal`. -/
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (PreservesLimit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `IsTerminal`. -/
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  ReflectsLimit.reflects ((isLimitMapConeEmptyConeEquiv G X).symm l)

/-- A functor that preserves and reflects terminal objects induces an equivalence on
`IsTerminal`. -/
def IsTerminal.isTerminalIffObj [PreservesLimit (Functor.empty.{0} C) G]
    [ReflectsLimit (Functor.empty.{0} C) G] (X : C) :
    IsTerminal X ≃ IsTerminal (G.obj X) where
  toFun := IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- Preserving the terminal object implies preserving all limits of the empty diagram. -/
def preservesLimitsOfShapePemptyOfPreservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty) G where
  preservesLimit :=
    preservesLimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasTerminal C]

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

/-- If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  haveI := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimitOfIso F.uniqueFromEmpty.symm⟩

variable [HasTerminal D]

/-- If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
def PreservesTerminal.ofIsoComparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty C) G := by
  apply preservesLimitOfPreservesLimitCone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIsIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.ofIsoComparison G

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
def preservesTerminalOfIso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty C) G :=
  preservesTerminalOfIsIso G f.hom

variable [PreservesLimit (Functor.empty.{0} C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).hom = terminalComparison G :=
  rfl

instance : IsIso (terminalComparison G) := by
  rw [← PreservesTerminal.iso_hom]
  infer_instance

end Terminal

section Initial

/-- The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def isColimitMapCoconeEmptyCoconeEquiv :
    IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving initial objects expressed in terms of `IsInitial`. -/
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) :
    IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (PreservesColimit.preserves l)

/-- The property of reflecting initial objects expressed in terms of `IsInitial`. -/
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) :
    IsInitial X :=
  ReflectsColimit.reflects ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

/-- A functor that preserves and reflects initial objects induces an equivalence on `IsInitial`. -/
def IsInitial.isInitialIffObj [PreservesColimit (Functor.empty.{0} C) G]
    [ReflectsColimit (Functor.empty.{0} C) G] (X : C) :
    IsInitial X ≃ IsInitial (G.obj X) where
  toFun := IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- Preserving the initial object implies preserving all colimits of the empty diagram. -/
def preservesColimitsOfShapePemptyOfPreservesInitial [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete PEmpty) G where
  preservesColimit :=
    preservesColimitOfIsoDiagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasInitial C]

/-- If `G` preserves the initial object and `C` has an initial object, then the image of the initial
object is initial.
-/
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)

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
    apply hasColimitOfIso F.uniqueFromEmpty⟩

variable [HasInitial D]

/-- If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
def PreservesInitial.ofIsoComparison [i : IsIso (initialComparison G)] :
    PreservesColimit (Functor.empty C) G := by
  apply preservesColimitOfPreservesColimitCocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
def preservesInitialOfIsIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] :
    PreservesColimit (Functor.empty C) G := by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.ofIsoComparison G

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥`, then `G` preserves initial objects. -/
def preservesInitialOfIso (f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Functor.empty C) G :=
  preservesInitialOfIsIso G f.hom

variable [PreservesColimit (Functor.empty.{0} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl

instance : IsIso (initialComparison G) := by
  rw [← PreservesInitial.iso_hom]
  infer_instance

end Initial

end CategoryTheory.Limits
