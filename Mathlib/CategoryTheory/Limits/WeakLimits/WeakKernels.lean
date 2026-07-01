/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Weak kernels

These are weak equalizes for functors of the form `ParallelPair f 0`.

If the category is preadditive, then weak equalizers exist if and only if weak kernels exist.
(See `hasWeakEqualizer_of_hasWeakKernel` and `hasWeakKernel_of_hasWeakEqualizer`.)

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroMorphisms C] {X Y : C} (f g : X ⟶ Y)

/-- A morphism `f` has a weak kernel if the functor `ParallelPair f 0` has a weak limit. -/
abbrev HasWeakKernel : Prop :=
  HasWeakLimit (parallelPair f 0)

variable (C) in
/-- `HasWeakKernels` represents the existence of weak kernels for every morphism. -/
class HasWeakKernels : Prop where
  hasWeakLimit : ∀ {X Y : C} (f : X ⟶ Y), HasWeakKernel f := by infer_instance

attribute [instance 100] HasWeakKernels.hasWeakLimit

/-- If a category has kernels, then it has weak kernels. -/
instance (priority := 100) HasWeakKernelsOfHasKernels [HasKernels C] :
    HasWeakKernels C where

section

variable [HasWeakKernel f]

/-- The weak kernel of a morphism. -/
abbrev weakKernel : C :=
  weakEqualizer f 0

/-- The map from `weakKernel f` into the source of `f`. -/
abbrev weakKernel.ι : weakKernel f ⟶ X :=
  weakEqualizer.ι f 0

@[simp]
theorem weakEqualizer_as_weakKernel : weakEqualizer.ι f 0 = weakKernel.ι f := rfl

@[reassoc (attr := simp)]
theorem weakKernel.condition : weakKernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The weak kernel built from `weakKernel.ι f` is weakly limiting. -/
def weakKernelIsWeakKernel :
    IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKernel.condition f).trans comp_zero.symm)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through
`weakKernel.ι f` via `weakKernel.lift : W ⟶ weakKernel f`. -/
abbrev weakKernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ weakKernel f :=
  (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
theorem weakKernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    weakKernel.lift f k h ≫ weakKernel.ι f = k :=
  (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ weakKernel f`
such that `l ≫ weakKernel.ι f = k`. -/
def weakKernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ weakKernel f // l ≫ weakKernel.ι f = k } :=
  ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

end

end Limits

namespace Preadditive

variable [Preadditive C] {X Y : C} {f g : X ⟶ Y}

/-- A weak kernel of `f - g` is a weak equalizer of `f` and `g`. -/
def isWeakLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsWeakLimit c) :
    IsWeakLimit (forkOfKernelFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]
theorem isWeakLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsWeakLimit c)
    (s : Fork f g) : (isWeakLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

/-- A weak equalizer of `f` and `g` is a weak kernel of `f - g`. -/
def isWeakLimitKernelForkOfFork {c : Fork f g} (i : IsWeakLimit c) :
    IsWeakLimit (kernelForkOfFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

variable (f g)

/-- A preadditive category has a weak equalizer for `f` and `g` if it has a weak
kernel for `f - g`. -/
theorem hasWeakEqualizer_of_hasWeakKernel [HasWeakKernel (f - g)] : HasWeakEqualizer f g :=
  HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

/-- A preadditive category has a weak kernel for `f - g` if it has a weak equalizer
for `f` and `g`. -/
theorem hasWeakKernel_of_hasWeakEqualizer [HasWeakEqualizer f g] : HasWeakKernel (f - g) :=
  HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

/-- If a preadditive category has all weak kernels, then it also has all weak equalizers. -/
theorem hasWeakEqualizers_of_hasWeakKernels [HasWeakKernels C] : HasWeakEqualizers C :=
  have {X Y : C} (f g : X ⟶ Y) := hasWeakEqualizer_of_hasWeakKernel f g
  hasWeakEqualizers_of_hasWeakLimit_parallelPair C

end Preadditive

end CategoryTheory
