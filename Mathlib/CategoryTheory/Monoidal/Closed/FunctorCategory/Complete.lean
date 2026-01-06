/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Lifting.Right
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Groupoid
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monad.Comonadicity
/-!

# Functors into a complete monoidal closed category form a monoidal closed category.

TODO (in progress by Joël Riou): make a more explicit construction of the internal hom in functor
categories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed Limits

noncomputable section

namespace CategoryTheory.Functor

section
variable (I : Type u₂) [Category.{v₂} I]

set_option backward.privateInPublic true in
private abbrev incl : Discrete I ⥤ I := Discrete.functor id

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

variable [∀ (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]
-- is also implied by: `[HasLimitsOfSize.{u₂, max u₂ v₂} C]`

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ReflectsIsomorphisms <| (whiskeringLeft _ _ C).obj (incl I) where
  reflects f h := by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩

variable [HasLimitsOfShape WalkingParallelPair C]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Comonad.PreservesLimitOfIsCoreflexivePair ((whiskeringLeft _ _ C).obj (incl I)) :=
  ⟨inferInstance⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ComonadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I)) :=
  Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
    ((incl I).ranAdjunction C)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance (F : I ⥤ C) : IsLeftAdjoint (tensorLeft (incl I ⋙ F)) :=
  (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Auxiliary definition for `functorCategoryMonoidalClosed` -/
def functorCategoryClosed (F : I ⥤ C) : Closed F :=
  have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  have := isLeftAdjoint_square_lift_comonadic (tensorLeft F) ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  { rightAdj := (tensorLeft F).rightAdjoint
    adj := Adjunction.ofIsLeftAdjoint (tensorLeft F) }

/--
Assuming the existence of certain limits, functors into a monoidal closed category form a
monoidal closed category.

Note: this is defined completely abstractly, and does not have any good definitional properties.
See the TODO in the module docstring.
-/
def functorCategoryMonoidalClosed : MonoidalClosed (I ⥤ C) where
  closed F := functorCategoryClosed I C F

end

end CategoryTheory.Functor
