/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Scalar multiplication on `Finsupp`

This file defines the pointwise scalar multiplication on `Finsupp`, assuming it preserves zero.

## Main declarations

* `Finsupp.smulZeroClass`: if the action of `R` on `M` preserves `0`, then it acts on `α →₀ M`

## Implementation notes

This file is intermediate between `Finsupp.Defs` and `Finsupp.Module` in that it covers scalar
multiplication but does not rely on the definition of `Module`. Scalar multiplication is needed to
supply the `nsmul` (and `zsmul`) fields of (semi)ring structures which are fundamental for e.g.
`Polynomial`, so we want to keep the imports required for the `Finsupp.smulZeroClass` instance
reasonably light.

This file is a `noncomputable theory` and uses classical logic throughout.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Module

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α →₀ M) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by
    ext
    apply smul_zero

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[simp, norm_cast]
theorem coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • ⇑v :=
  rfl

theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl

instance instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (α →₀ M) where
  zero_smul f := by ext i; exact zero_smul _ _

variable (α M)

instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (α →₀ M) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

instance isScalarTower [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S]
    [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance smulCommClass [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommClass R S M] :
    SMulCommClass R S (α →₀ M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance isCentralScalar [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (α →₀ M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

variable {α M}

theorem support_smul [Zero M] [SMulZeroClass R M] {b : R} {g : α →₀ M} :
    (b • g).support ⊆ g.support := fun a => by
  simp only [smul_apply, mem_support_iff, Ne]
  exact mt fun h => h.symm ▸ smul_zero _

@[simp]
theorem smul_single [Zero M] [SMulZeroClass R M] (c : R) (a : α) (b : M) :
    c • Finsupp.single a b = Finsupp.single a (c • b) :=
  mapRange_single

theorem mapRange_smul' [Zero M] [SMulZeroClass R M] [Zero N]
    [SMulZeroClass S N] {f : M → N} {hf : f 0 = 0} (c : R) (d : S) (v : α →₀ M)
    (hsmul : ∀ x, f (c • x) = d • f x) : mapRange f hf (c • v) = d • mapRange f hf v := by
  ext
  simp [hsmul]

theorem mapRange_smul [Zero M] [SMulZeroClass R M] [Zero N]
    [SMulZeroClass R N] {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M)
    (hsmul : ∀ x, f (c • x) = c • f x) : mapRange f hf (c • v) = c • mapRange f hf v :=
  mapRange_smul' c c v hsmul

end Finsupp
