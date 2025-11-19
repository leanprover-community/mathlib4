/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Product of torsion-free modules

This file shows that the product of two torsion-free modules is torsion-free.
-/

@[expose] public section

open Module

variable {R M N : Type*}

namespace Prod

instance moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [IsTorsionFree R M] [IsTorsionFree R N] :
    IsTorsionFree R (M × N) where
  isSMulRegular _r hr := hr.isSMulRegular.prodMap hr.isSMulRegular

end Prod
