/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Order.WithBot.Basic

/-!
# Basic equivalences involving `WithBot α` or `WithTop α`.
-/

namespace Equiv

/-- The set of `x : WithBot α` such that `x ≠ ⊥` is equivalent to `α`. -/
@[simps]
def withBotNeBot (α) : { x : WithBot α // x ≠ ⊥ } ≃ α where
  toFun o := WithBot.unbot _ o.2
  invFun x := ⟨.some x, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The set of `x : WithTop α` such that `x ≠ ⊤` is equivalent to `α`. -/
@[simps]
def withTopNeTop (α) : { x : WithTop α // x ≠ ⊤ } ≃ α where
  toFun o := WithTop.untop _ o.2
  invFun x := ⟨.some x, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

end Equiv
