/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Martin C. Martin
-/
import Mathlib.Algebra.Module.Basic

/-!
# Minimal Axioms for a Module

This file defines a constructor to define a `Module` structure on a Type with an
AddCommGroup, while proving a minimum number of equalities.

## Main Definitions

* `Module.ofMinimalAxioms`: Define a `Module` structure on a Type with an
  AddCommGroup by proving a minimized set of axioms

-/

variable (R M) [Semiring R] [AddCommGroup M]

/-- A structure containing most informations as in a module, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `AddCommGroup`,
this provides a way to construct a module structure by checking less properties, in
`Module.ofMinimalAxioms`. -/
-- Porting note: removed @[nolint has_nonempty_instance]
structure Module.Core extends SMul R M where
  /-- Scalar multiplication distributes over addition from the left. -/
  smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
  /-- Scalar multiplication distributes over addition from the right. -/
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication distributes over multiplication from the right. -/
  mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x
  /-- Scalar multiplication by one is the identity. -/
  one_smul : ∀ x : M, (1 : R) • x = x
#align module.core Module.Core

variable {R M}

/-- Define `Module` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `Module.Core`, when the underlying space is an `AddCommGroup`. -/
def Module.ofMinimalAxioms (H : Module.Core R M) : Module R M :=
  letI := H.toSMul
  { H with
    zero_smul := fun x =>
      (AddMonoidHom.mk' (fun r : R => r • x) fun r s => H.add_smul r s x).map_zero
    smul_zero := fun r => (AddMonoidHom.mk' ((· • ·) r) (H.smul_add r)).map_zero }
#align module.of_core Module.ofMinimalAxioms
