/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Pi

/-!
# Product of torsion-free modules

This file shows that the product of torsion-free modules is torsion-free.
-/

@[expose] public section

open Module

variable {ι R : Type*} {M : ι → Type*}

namespace Pi

instance instModuleIsTorsionFree [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, IsTorsionFree R (M i)] : Module.IsTorsionFree R (∀ i, M i) where
  isSMulRegular _r hr := .piMap fun _i ↦ hr.isSMulRegular

end Pi
