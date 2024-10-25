/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Finite.Prod

/-!
# Finite types

In this file we prove some theorems about `Finite` and provide some instances. This typeclass is a
`Prop`-valued counterpart of the typeclass `Fintype`. See more details in the file where `Finite` is
defined.

## Main definitions

* `Fintype.finite`, `Finite.of_fintype` creates a `Finite` instance from a `Fintype` instance. The
  former lemma takes `Fintype α` as an explicit argument while the latter takes it as an instance
  argument.
* `Fintype.of_finite` noncomputably creates a `Fintype` instance from a `Finite` instance.

## Implementation notes

There is an apparent duplication of many `Fintype` instances in this module,
however they follow a pattern: if a `Fintype` instance depends on `Decidable`
instances or other `Fintype` instances, then we need to "lower" the instance
to be a `Finite` instance by removing the `Decidable` instances and switching
the `Fintype` instances to `Finite` instances. These are precisely the ones
that cannot be inferred using `Finite.of_fintype`. (However, when using
`open scoped Classical` or the `classical` tactic the instances relying only
on `Decidable` instances will give `Finite` instances.) In the future we might
consider writing automation to create these "lowered" instances.

## Tags

finiteness, finite types
-/

open Mathlib

variable {α β : Type*}
namespace Finite

-- see Note [lower instance priority]
instance (priority := 100) of_subsingleton {α : Sort*} [Subsingleton α] : Finite α :=
  of_injective (Function.const α ()) <| Function.injective_of_subsingleton _

-- Higher priority for `Prop`s
-- Porting note(#12096): removed @[nolint instance_priority], linter not ported yet
instance prop (p : Prop) : Finite p :=
  Finite.of_subsingleton

end Finite

instance Quot.finite {α : Sort*} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ (surjective_quot_mk r)

instance Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _

instance Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β) := by
  cases' isEmpty_or_nonempty (α ↪ β) with _ h
  · -- Porting note: infer_instance fails because it applies `Finite.of_fintype` and produces a
    -- "stuck at solving universe constraint" error.
    apply Finite.of_subsingleton

  · refine h.elim fun f => ?_
    haveI : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective

instance Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β) :=
  Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext <| by
    convert DFunLike.congr_fun h using 0

instance Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
