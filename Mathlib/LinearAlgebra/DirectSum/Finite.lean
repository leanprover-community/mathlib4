/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# A finite direct sum of finite modules is finite

This file defines a `Module.Finite` instance for a finite direct sum of finite modules.

-/

variable {R : Type*} [Semiring R] {ι : Type*} [_root_.Finite ι]
variable (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]

instance Module.Finite.dfinsupp [∀ (i : ι), Module.Finite R (M i)] :
    Module.Finite R (Π₀ (i : ι), M i) :=
  letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm

open DirectSum

variable (R : Type*) [Semiring R] {ι : Type*} [Finite ι] (M : ι → Type*)
  [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]

instance Module.Finite.directSum [∀ i : ι, Module.Finite R (M i)] : Module.Finite R (⨁ i, M i) := by
  dsimp [DirectSum]
  infer_instance
