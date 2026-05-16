/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Adjoint functors preserve Kan extensions

In this file, it is shown that left adjoint functors preserve left Kan extensions,
and that right adjoint functors preserve right Kan extensions.
In particuliar, this applies to equivalences of categories.

-/

@[expose] public section

namespace CategoryTheory

open Functor Limits

variable {C D H₁ H₂ : Type*} [Category* C] [Category* D] [Category* H₁] [Category* H₂]
  {G₁ : H₁ ⥤ H₂} {G₂ : H₂ ⥤ H₁}

namespace Adjunction

variable (adj : G₁ ⊣ G₂)

section

variable (F : C ⥤ H₁) (L : C ⥤ D)

/-- The right adjoint of `LeftExtension.postcompose₂ L F G₁` when `G₁` is
part of an adjunction `adj : G₁ ⊣ G₂`. -/
@[simps!]
def leftExtensionPostCompose₂RightAdjoint :
    L.LeftExtension (F ⋙ G₁) ⥤ L.LeftExtension F :=
  StructuredArrow.map₂ (F := (whiskeringRight _ _ _).obj G₂)
    (G := (whiskeringRight _ _ _).obj G₂)
    (F.rightUnitor.inv ≫ whiskerLeft F adj.unit ≫ (associator _ _ _).inv)
    { app _ := (associator _ _ _).hom }

/-- The adjunction exhibiting that `LeftExtension.postcompose₂ L F G₁` has a right adjoint
when `G₁` has. -/
def leftExtensionPostcompose₂ :
    LeftExtension.postcompose₂ L F G₁ ⊣ adj.leftExtensionPostCompose₂RightAdjoint F L where
  unit.app E := StructuredArrow.homMk (whiskerLeft E.right adj.unit)
  counit.app E := StructuredArrow.homMk (whiskerLeft E.right adj.counit)

include adj in
lemma preservesLeftKanExtension : G₁.PreservesLeftKanExtension F L where
  preserves F' α hα := by
    have := (adj.leftExtensionPostcompose₂ F L).isLeftAdjoint
    rw [Functor.isLeftKanExtension_iff] at hα ⊢
    refine ⟨(IsInitial.equivOfIso ?_).1
      (IsInitial.isInitialObj (LeftExtension.postcompose₂ L F G₁) _ hα.some)⟩
    exact StructuredArrow.isoMk (Iso.refl _)

end

section

variable (F : C ⥤ H₂) (L : C ⥤ D)

/-- The left adjoint of `RightExtension.postcompose₂ L F G₂` when `G₂` is
part of an adjunction `adj : G₁ ⊣ G₂`. -/
@[simps!]
def rightExtensionPostCompose₂LeftAdjoint :
    L.RightExtension (F ⋙ G₂) ⥤ L.RightExtension F :=
  CostructuredArrow.map₂ (F := (whiskeringRight _ _ _).obj G₁)
    (G := (whiskeringRight _ _ _).obj G₁) { app _ := (associator _ _ _).inv }
    ((associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom)

/-- The adjunction exhibiting that `RightExtension.postcompose₂ L F G₂` has a left adjoint
when `G₂` has. -/
def rightExtensionPostcompose₂ :
    adj.rightExtensionPostCompose₂LeftAdjoint F L ⊣  RightExtension.postcompose₂ L F G₂ where
  unit.app E := CostructuredArrow.homMk (whiskerLeft E.left adj.unit)
  counit.app E := CostructuredArrow.homMk (whiskerLeft E.left adj.counit)

include adj in
lemma preservesRightKanExtension : G₂.PreservesRightKanExtension F L where
  preserves F' α hα := by
    have := (adj.rightExtensionPostcompose₂ F L).isRightAdjoint
    rw [Functor.isRightKanExtension_iff] at hα ⊢
    refine ⟨(IsTerminal.equivOfIso ?_).1
      (IsTerminal.isTerminalObj (RightExtension.postcompose₂ L F G₂) _ hα.some)⟩
    exact CostructuredArrow.isoMk (Iso.refl _)

end

end Adjunction

namespace Functor

instance [G₁.IsLeftAdjoint] (F : C ⥤ H₁) (L : C ⥤ D) :
    G₁.PreservesLeftKanExtension F L :=
  (Adjunction.ofIsLeftAdjoint G₁).preservesLeftKanExtension F L

instance [G₂.IsRightAdjoint] (F : C ⥤ H₂) (L : C ⥤ D) :
    G₂.PreservesRightKanExtension F L :=
  (Adjunction.ofIsRightAdjoint G₂).preservesRightKanExtension F L

end Functor

end CategoryTheory
