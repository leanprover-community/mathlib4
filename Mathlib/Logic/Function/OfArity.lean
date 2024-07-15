/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Mathport.Rename
import Mathlib.Logic.Function.FromTypes

/-! # Function types of a given arity

This provides `Function.OfArity`, such that `OfArity α β 2 = α → α → β`.
Note that it is often preferable to use `(Fin n → α) → β` in place of `OfArity n α β`.

## Main definitions

* `Function.OfArity α β n`: `n`-ary function `α → α → ... → β`. Defined inductively.
* `Function.OfArity.const α b n`: `n`-ary constant function equal to `b`.
-/

universe u

namespace Function

/-- The type of `n`-ary functions `α → α → ... → β`.

Note that this is not universe polymorphic, as this would require that when `n=0` we produce either
`Unit → β` or `ULift β`. -/
abbrev OfArity (α β : Type u) (n : ℕ) : Type u := FromTypes (fun (_ : Fin n) => α) β
#align arity Function.OfArity

@[simp]
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β := fromTypes_zero _ _
#align arity_zero Function.ofArity_zero

@[simp]
theorem ofArity_succ (α β : Type u) (n : ℕ) :
    OfArity α β n.succ = (α → OfArity α β n) := fromTypes_succ _ _
#align arity_succ Function.ofArity_succ

namespace OfArity

/-- Constant `n`-ary function with value `b`. -/
def const (α : Type u) {β : Type u} (b : β) (n : ℕ) : OfArity α β n :=
  FromTypes.const (fun _ => α) b
#align arity.const Function.OfArity.const

@[simp]
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  FromTypes.const_zero (fun _ => α) b
#align arity.const_zero Function.OfArity.const_zero

@[simp]
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : ℕ) :
    const α b n.succ = fun _ => const _ b n :=
  FromTypes.const_succ (fun _ => α) b
#align arity.const_succ Function.OfArity.const_succ

theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : ℕ) (x : α) :
    const α b n.succ x = const _ b n := FromTypes.const_succ_apply _ b x
#align arity.const_succ_apply Function.OfArity.const_succ_apply

instance inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))
#align arity.arity.inhabited Function.OfArity.inhabited

end OfArity

namespace FromTypes

lemma fromTypes_fin_const (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β = OfArity α β n := rfl

/-- The definitional equality between heterogeneous functions with constant
domain and `n`-ary functions with that domain. -/
def fromTypes_fin_const_equiv (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β ≃ OfArity α β n := .refl _

end FromTypes

end Function
