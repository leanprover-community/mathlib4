/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Martin C. Martin
-/
import Mathlib.Algebra.Module.Defs

/-!
# Minimal Axioms for a Module

This file defines a constructor to define a `Module` structure on a Type with an
`AddCommGroup`, while proving a minimum number of equalities.

## Main Definitions

* `Module.ofMinimalAxioms`: Define a `Module` structure on a Type with an
  AddCommGroup by proving a minimized set of axioms

-/

universe u v

/-- Define a `Module` structure on a Type by proving a minimized set of axioms. -/
abbrev Module.ofMinimalAxioms {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [SMul R M]
    -- Scalar multiplication distributes over addition from the left.
    (smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y)
    -- Scalar multiplication distributes over addition from the right.
    (add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x)
    -- Scalar multiplication distributes over multiplication from the right.
    (mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x)
    -- Scalar multiplication by one is the identity.
    (one_smul : ∀ x : M, (1 : R) • x = x) : Module R M :=
  { smul_add := smul_add,
    add_smul := add_smul,
    mul_smul := mul_smul,
    one_smul := one_smul,
    zero_smul := fun x =>
      (AddMonoidHom.mk' (· • x) fun r s => add_smul r s x).map_zero
    smul_zero := fun r => (AddMonoidHom.mk' (r • ·) (smul_add r)).map_zero }
#align module.of_core Module.ofMinimalAxioms
