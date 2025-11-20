/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.WithBot.Basic

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/

@[expose] public section

variable {α : Type*}

instance [Fintype α] : Fintype (WithTop α) :=
  Fintype.ofEquiv (Option α) WithTop.equivOption.symm

instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

instance [Infinite α] : Infinite (WithTop α) :=
  Infinite.of_injective _ WithTop.equivOption.symm.injective

instance [Fintype α] : Fintype (WithBot α) :=
  Fintype.ofEquiv (Option α) WithBot.equivOption.symm

instance [Finite α] : Finite (WithBot α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

instance [Infinite α] : Infinite (WithBot α) :=
  Infinite.of_injective _ WithBot.equivOption.symm.injective
