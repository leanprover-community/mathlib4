/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Weak equalizers

These are weak limits for diagrams of shape `WalkingParallelPair`.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {X Y : C} (f g : X ⟶ Y)

/-- Two parallel morphisms `f` and `g` have a weak equalizer if the diagram `parallelPair f g`
has a weak limit. -/
abbrev HasWeakEqualizer :=
  HasWeakLimit (parallelPair f g)

variable [HasWeakEqualizer f g]

/-- If a weak equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `weakEqualizer f g`. -/
noncomputable abbrev weakEqualizer : C :=
  weakLimit (parallelPair f g)

/-- If a weak equalizer of `f` and `g` exists, we can access the morphism
`weakEqualizer f g ⟶ X` by saying `weakEqualizer.ι f g`. -/
noncomputable abbrev weakEqualizer.ι : weakEqualizer f g ⟶ X :=
  weakLimit.π (parallelPair f g) WalkingParallelPair.zero

/-- A weak equalizer cone for a parallel pair `f` and `g` -/
noncomputable abbrev weakEqualizer.fork : Fork f g :=
  weakLimit.cone (parallelPair f g)

@[simp]
theorem weakEqualizer.fork_ι : (weakEqualizer.fork f g).ι = weakEqualizer.ι f g :=
  rfl

@[simp]
theorem weakEqualizer.fork_π_app_zero :
    (weakEqualizer.fork f g).π.app WalkingParallelPair.zero = weakEqualizer.ι f g :=
  rfl

@[reassoc]
theorem weakEqualizer.condition : weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g :=
  Fork.condition <| weakLimit.cone <| parallelPair f g

set_option backward.defeqAttrib.useBackward true in
/-- The weak equalizer built from `weakEqualizer.ι f g` is weakly limiting. -/
def weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
    (weakEqualizer.condition f g)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the weak equalizer of
`f` and `g` via `weakEqualizer.lift : W ⟶ weakEqualizer f g`. -/
noncomputable abbrev weakEqualizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ weakEqualizer f g :=
  weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
theorem weakEqualizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    weakEqualizer.lift k h ≫ weakEqualizer.ι f g = k :=
  weakLimit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakEqualizer f g` satisfying `l ≫ weakEqualizer.ι f g = k`. -/
def weakEqualizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ weakEqualizer f g // l ≫ weakEqualizer.ι f g = k } :=
  ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

variable (C)

/-- A category `HasWeakEqualizers` if it has all weak limits of shape `WalkingParallelPair`,
i.e. if it has a weak equalizer for every parallel pair of morphisms. -/
abbrev HasWeakEqualizers :=
  HasWeakLimitsOfShape WalkingParallelPair C

/-- A category with equalizers has weak equalizers. -/
instance (priority := 100) HasWeakEqualizersOfHasEqualizers [HasEqualizers C] :
    HasWeakEqualizers C where

/-- If `C` has all weak limits of diagrams `parallelPair f g`, then it has all weak equalizers -/
theorem hasWeakEqualizers_of_hasWeakLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasWeakLimit (parallelPair f g)] : HasWeakEqualizers C where
      hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoParallelPair F).symm

variable {C}

/-- This is a slightly more convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
def Fork.IsWeakLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsWeakLimit t :=
  { lift
    fac s j :=
      WalkingParallelPair.casesOn j (fac s) <| by
        simp [← Category.assoc, fac] }

/-- This is another convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def Fork.IsWeakLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι}) :
    IsWeakLimit t :=
  Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

end CategoryTheory.Limits
