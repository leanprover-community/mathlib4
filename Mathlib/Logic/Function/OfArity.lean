/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename

/-! # Function types of a given arity

This provides `FunctionOfArity`, such that `OfArity α β 2 = α → α → β`.
Note that it is often preferrable to use `(Fin n → α) → β` in place of `OfArity n α β`.

## Main definitions

* `Function.OfArity α β n`: `n`-ary function `α → α → ... → β`. Defined inductively.
* `Function.OfArity.const α b n`: `n`-ary constant function equal to `b`.
-/

universe u

namespace Function

/-- The type of `n`-ary functions `α → α → ... → β`.

Note that this is not universe polymorphic, as this would require that when `n=0` we produce either
`Unit → β` or `ULift β`. -/
def OfArity (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → OfArity α β n
#align arity Function.OfArity

@[simp]
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β :=
  rfl
#align arity_zero Function.ofArity_zero

@[simp]
theorem ofArity_succ (α β : Type u) (n : ℕ) : OfArity α β n.succ = (α → OfArity α β n) :=
  rfl
#align arity_succ Function.ofArity_succ

namespace OfArity

/-- Constant `n`-ary function with value `a`. -/
def const (α : Type u) {β : Type u} (b : β) : ∀ n, OfArity α β n
  | 0 => b
  | n + 1 => fun _ => const _ b n
#align arity.const Function.OfArity.const

@[simp]
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  rfl
#align arity.const_zero Function.OfArity.const_zero

@[simp]
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : ℕ) :
    const α b n.succ = fun _ => const _ b n :=
  rfl
#align arity.const_succ Function.OfArity.const_succ

theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : ℕ) (x : α) :
    const α b n.succ x = const _ b n :=
  rfl
#align arity.const_succ_apply Function.OfArity.const_succ_apply

instance OfArity.inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  ⟨const _ default _⟩
#align arity.arity.inhabited Function.OfArity.OfArity.inhabited

end OfArity

end Function
