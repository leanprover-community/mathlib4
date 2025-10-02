/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Order.WithBot.Basic

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/

variable {α : Type*}

instance [Fintype α] : Fintype (WithTop α) :=
  Fintype.ofEquiv (Option α) WithTop.equivOption.symm

instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

instance [Fintype α] : Fintype (WithBot α) :=
  Fintype.ofEquiv (Option α) WithBot.equivOption.symm

instance [Finite α] : Finite (WithBot α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
