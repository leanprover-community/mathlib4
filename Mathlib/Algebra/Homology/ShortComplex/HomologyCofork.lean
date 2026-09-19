/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The homology functor as a cokernel and as a kernel

In this file, we show that in the category of functors `ShortComplex C ⥤ C`,
- the functor `cyclesFunctor C` is the kernel of `π₂ ⟶ π₃`;
- the functor `opcyclesFunctor C` is the cokernel of `π₁ ⟶ π₂`;
- the functor `homologyFunctor C` is the cokernel of `π₁ ⟶ cyclesFunctor C`;
- the functor `homologyFunctor C` is the kernel of `opcyclesFunctor C ⟶ π₃`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable (C : Type*) [Category* C]

namespace ShortComplex

section

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

set_option backward.isDefEq.respectTransparency false in
/-- The limit kernel fork expressing `cyclesFunctor C : ShortComplex C ⥤ C`
as the kernel of `π₂Toπ₃ : π₂ ⟶ π₃`. -/
@[implicit_reducible]
noncomputable def cyclesFunctorFork :
    KernelFork (ShortComplex.π₂Toπ₃ (C := C)) :=
  KernelFork.ofι (iCyclesNatTrans C) (by cat_disch)

/-- The functor `cyclesFunctor C : ShortComplex C ⥤ C` is the kernel of `π₂Toπ₃ : π₂ ⟶ π₃`. -/
@[no_expose]
noncomputable def isLimitCyclesFunctorFork :
    IsLimit (cyclesFunctorFork C) :=
  evaluationJointlyReflectsLimits _
    (fun S ↦ (KernelFork.isLimitMapConeEquiv _ _).2 S.cyclesIsKernel)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit cokernel cofork expressing `opcyclesFunctor C : ShortComplex C ⥤ C`
as the cokernel of `π₁Toπ₂ : π₁ ⟶ π₂`. -/
@[implicit_reducible]
noncomputable def opcyclesFunctorCofork :
    CokernelCofork (ShortComplex.π₁Toπ₂ (C := C)) :=
  CokernelCofork.ofπ (pOpcyclesNatTrans C) (by cat_disch)

/-- The functor `opcyclesFunctor C : ShortComplex C ⥤ C` is the cokernel of `π₁Toπ₂ : π₁ ⟶ π₂`. -/
@[no_expose]
noncomputable def isColimitOpcyclesFunctorCofork :
    IsColimit (opcyclesFunctorCofork C) :=
  evaluationJointlyReflectsColimits _
    (fun S ↦ (CokernelCofork.isColimitMapCoconeEquiv _ _).2 S.opcyclesIsCokernel)

end

section

variable [HasZeroMorphisms C] [CategoryWithHomology C]

set_option backward.isDefEq.respectTransparency false in
/-- The colimit cokernel cofork expressing `homologyFunctor C : ShortComplex C ⥤ C`
as the cokernel of `toCyclesNatTrans C : π₁ ⟶ cyclesFunctor C`. -/
@[implicit_reducible]
noncomputable def homologyFunctorCofork : CokernelCofork (toCyclesNatTrans C) :=
  CokernelCofork.ofπ (homologyπNatTrans C) (by cat_disch)

/-- The functor `homologyFunctor C : ShortComplex C ⥤ C` is
the cokernel of `toCyclesNatTrans C : π₁ ⟶ cyclesFunctor C`. -/
@[no_expose]
noncomputable def isColimitHomologyFunctorCofork :
    IsColimit (homologyFunctorCofork C) :=
  evaluationJointlyReflectsColimits _
    (fun S ↦ (CokernelCofork.isColimitMapCoconeEquiv _ _).2 S.homologyIsCokernel)

set_option backward.isDefEq.respectTransparency false in
/-- The limit kernel fork expressing `homologyFunctor C : ShortComplex C ⥤ C`
as the kernel of `fromOpcyclesNatTrans C : opcyclesFunctor C ⟶ π₃`. -/
@[implicit_reducible]
noncomputable def homologyFunctorFork : KernelFork (fromOpcyclesNatTrans C) :=
  KernelFork.ofι (homologyιNatTrans C) (by cat_disch)

/-- The functor `homologyFunctor C : ShortComplex C ⥤ C` is
the kernel of `fromOpcyclesNatTrans C : opcyclesFunctor C ⟶ π₃`. -/
@[no_expose]
noncomputable def isLimitHomologyFunctorFork :
    IsLimit (homologyFunctorFork C) :=
  evaluationJointlyReflectsLimits _
    (fun S ↦ (KernelFork.isLimitMapConeEquiv _ _).2 S.homologyIsKernel)

end

end ShortComplex

end CategoryTheory
