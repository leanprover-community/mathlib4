/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Logic.Embedding.Basic
import Mathlib.Order.WithBot.Basic

/-!
# Embedding into `WithBot  α` using `some`.
-/

namespace Function.Embedding

/-- Embedding into `WithTop α` using `some`. -/
@[simps -fullyApplied]
protected def withTop {α} : α ↪ WithTop α :=
  ⟨WithTop.some, WithTop.coe_injective⟩

/-- A version of `WithTop.map` for `Function.Embedding`s. -/
@[simps -fullyApplied]
def withTopMap {α β} (f : α ↪ β) : WithTop α ↪ WithTop β :=
  ⟨WithTop.map f, WithTop.map_injective f.injective⟩

/-- Embedding into `WithBot α` using `some`. -/
@[simps -fullyApplied]
protected def withBot {α} : α ↪ WithBot α :=
  ⟨WithBot.some, WithBot.coe_injective⟩

/-- A version of `WithTop.map` for `Function.Embedding`s. -/
@[simps -fullyApplied]
def withBotMap {α β} (f : α ↪ β) : WithBot α ↪ WithBot β :=
  ⟨WithBot.map f, WithBot.map_injective f.injective⟩

end Function.Embedding
