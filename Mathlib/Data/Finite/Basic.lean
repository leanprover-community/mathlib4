/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Vector

#align_import data.finite.basic from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

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


noncomputable section

open scoped Classical

variable {α β γ : Type*}

namespace Finite

-- see Note [lower instance priority]
instance (priority := 100) of_subsingleton {α : Sort*} [Subsingleton α] : Finite α :=
  of_injective (Function.const α ()) <| Function.injective_of_subsingleton _
#align finite.of_subsingleton Finite.of_subsingleton

-- Higher priority for `Prop`s
-- Porting note(#12096): removed @[nolint instance_priority], linter not ported yet
instance prop (p : Prop) : Finite p :=
  Finite.of_subsingleton
#align finite.prop Finite.prop

instance [Finite α] [Finite β] : Finite (α × β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

instance {α β : Sort*} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm

theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective
#align finite.prod_left Finite.prod_left

theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective
#align finite.prod_right Finite.prod_right

instance [Finite α] [Finite β] : Finite (Sum α β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

theorem sum_left (β) [Finite (Sum α β)] : Finite α :=
  of_injective (Sum.inl : α → Sum α β) Sum.inl_injective
#align finite.sum_left Finite.sum_left

theorem sum_right (α) [Finite (Sum α β)] : Finite β :=
  of_injective (Sum.inr : β → Sum α β) Sum.inr_injective
#align finite.sum_right Finite.sum_right

instance {β : α → Type*} [Finite α] [∀ a, Finite (β a)] : Finite (Σa, β a) := by
  letI := Fintype.ofFinite α
  letI := fun a => Fintype.ofFinite (β a)
  infer_instance

instance {ι : Sort*} {π : ι → Sort*} [Finite ι] [∀ i, Finite (π i)] : Finite (Σ'i, π i) :=
  of_equiv _ (Equiv.psigmaEquivSigmaPLift π).symm

instance [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

end Finite

instance Pi.finite {α : Sort*} {β : α → Sort*} [Finite α] [∀ a, Finite (β a)] :
    Finite (∀ a, β a) := by
  haveI := Fintype.ofFinite (PLift α)
  haveI := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (∀ a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)
#align pi.finite Pi.finite

instance Vector.finite {α : Type*} [Finite α] {n : ℕ} : Finite (Vector α n) := by
  haveI := Fintype.ofFinite α
  infer_instance
#align vector.finite Vector.finite

instance Quot.finite {α : Sort*} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ (surjective_quot_mk r)
#align quot.finite Quot.finite

instance Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _
#align quotient.finite Quotient.finite

instance Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β) := by
  cases' isEmpty_or_nonempty (α ↪ β) with _ h
  · -- Porting note: infer_instance fails because it applies `Finite.of_fintype` and produces a
    -- "stuck at solving universe constraint" error.
    apply Finite.of_subsingleton

  · refine h.elim fun f => ?_
    haveI : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective
#align function.embedding.finite Function.Embedding.finite

instance Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β) :=
  Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext <| by
    convert DFunLike.congr_fun h using 0
#align equiv.finite_right Equiv.finite_right

instance Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
#align equiv.finite_left Equiv.finite_left

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  haveI := Fintype.ofFinite α
  infer_instance
