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

open DirectSum

section Semiring

variable (R : Type*) [Semiring R] {ι : Type*} [Finite ι] (M : ι → Type*)
  [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]

instance Module.Finite.directSum [∀ i : ι, Module.Finite R (M i)] : Module.Finite R (⨁ i, M i) := by
  dsimp [DirectSum]
  infer_instance

end Semiring
