/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels

/-!
# Weak kernels in pretriangulated categories

We prove that pretriangulated categories have weak kernels: if `f : X ⟶ Y` is a morphism in
a pretriangulated category and if we complete it to a distinguished triangle
`Z ⟶ X ⟶ Y ⟶ Z⟦1⟧`, then the first morphism `Z ⟶ Y` of that triangle is a weak kernel of `f`.

TODO: Weak cokernels.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Pretriangulated

open Limits Category Preadditive Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- If `T` is a distinguished triangle, then `T.mor₁` defines a kernel fork for `T.mor₂`. -/
def kernelForkOfDistTriangle (T : Triangle C) (dT : T ∈ distTriang C) :
    KernelFork T.mor₂ := KernelFork.ofι T.mor₁ (comp_distTriang_mor_zero₁₂ _ dT)

/-- If `T` is a distinguished triangle, then the kernel fork for `T.mor₂` defined in
`kernelForkOfDistTriangle` is a weak kernel fork. -/
def isWeakLimitKernelForkOfDistTriangle (T : Triangle C) (dT : T ∈ distTriang C) :
    IsWeakLimit (kernelForkOfDistTriangle _ dT) :=
  Fork.IsWeakLimit.mk' _
    (fun s ↦ ⟨_, (T.coyoneda_exact₂ dT _ (KernelFork.condition s)).choose_spec.symm⟩)

/-- A pretriangulated category has weak kernels. -/
instance : HasWeakKernels C where
  hasWeakLimit f := ⟨by
    obtain ⟨K, i, p, h⟩ := distinguished_cocone_triangle₁ f
    exact ⟨_, isWeakLimitKernelForkOfDistTriangle _ h⟩⟩

end CategoryTheory.Pretriangulated
