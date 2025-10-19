/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# (Co)kernels in functor categories
-/

namespace CategoryTheory.Limits
universe u
variable (C : Type*) [Category.{u} C] [HasZeroMorphisms C]

/-- The kernel fork is itself a kernel. -/
noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
  evaluationJointlyReflectsLimits _ fun f ↦ (KernelFork.isLimitMapConeEquiv ..).2 <|
    (kernelIsKernel f.hom).ofIsoLimit <| Fork.ext <| .refl _

/-- The cokernel cofork is itself a cokernel. -/
noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
  evaluationJointlyReflectsColimits _ fun f ↦ (CokernelCofork.isColimitMapCoconeEquiv ..).2 <|
    (cokernelIsCokernel f.hom).ofIsoColimit <| Cofork.ext <| .refl _

end CategoryTheory.Limits
