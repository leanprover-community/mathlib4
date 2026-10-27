/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.FunLike
public import Mathlib.Algebra.Module.FunLikeSMul

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

public section

assert_not_exists Module

noncomputable section

open Finset Function

variable {α M N R S : Type*}

namespace Finsupp

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α →₀ M) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by
    ext
    apply smul_zero

instance [Zero M] [SMulZeroClass R M] : IsSMulApply R (α →₀ M) where

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[deprecated FunLike.coe_smul +typeChanged (since := "2026-10-27")]
theorem coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • ⇑v :=
  rfl

@[deprecated smul_apply +typeChanged (since := "2026-10-27")]
protected theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl

instance instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (α →₀ M) :=
  FunLike.smulWithZero

variable (α M)

instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (α →₀ M) :=
  FunLike.distribSMul

instance isScalarTower [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S]
    [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) :=
  FunLike.isScalarTower

instance smulCommClass [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommClass R S M] :
    SMulCommClass R S (α →₀ M) :=
  FunLike.smulCommClass

instance isCentralScalar [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (α →₀ M) :=
  FunLike.isCentralScalar

variable {α M}

theorem support_smul [Zero M] [SMulZeroClass R M] {b : R} {g : α →₀ M} :
    (b • g).support ⊆ g.support := fun a => by
  simp only [mem_support_iff, Ne, smul_apply]
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
