/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Order.Defs

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# Unbundled algebra classes

These classes are part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).
However a subset of them are widely used in mathlib3,
and it has been tricky to clean this up as this file was in core Lean 3.

By themselves, these classes are not good replacements for the `Monoid` / `Group` etc structures
provided by mathlib, as they are not discoverable by `simp` unlike the current lemmas due to there
being little to index on. The Wiki page linked above describes an algebraic normalizer, but it was
never implemented in Lean 3.

## Porting note:
This file is ancient, and it would be good to replace it with a clean version
that provides what mathlib4 actually needs.

I've omitted all the `@[algebra]` attributes, as they are not used elsewhere.

The section `StrictWeakOrder` has been omitted, but I've left the mathport output in place.
Please delete if cleaning up.

I've commented out some classes which we think are completely unused in mathlib.

I've added many of the declarations to `nolints.json`.
If you clean up this file, please add documentation to classes that we are keeping.

Mario made the following analysis of uses in mathlib3:
* `is_symm_op`: unused except for some instances
* `is_commutative`: used a fair amount via some theorems about folds
  (also assuming `is_associative`)
* `is_associative`: ditto, also used in `noncomm_fold`
* `is_left_id`, `is_right_id`: unused except in the mathlib class `is_unital` and in `mono`
  (which looks like it could use `is_unital`)
* `is_left_null`, `is_right_null`: unused
* `is_left_cancel`, `is_right_cancel`: unused except for instances
* `is_idempotent`: this one is actually used to prove things not directly about `is_idempotent`
* `is_left_distrib`, `is_right_distrib`, `is_left_inv`, `is_right_inv`, `is_cond_left_inv`,
  `is_cond_right_inv`: unused
* `is_distinct`: unused (although we reinvented this one as `nontrivial`)
* `is_irrefl`, `is_refl`, `is_symm`, `is_trans`: significant usage
* `is_asymm`, `is_antisymm`, `is_total`, `is_strict_order`: a lot of uses but all in order theory
  and it's unclear how much could not be transferred to another typeclass
* `is_preorder`: unused except for instances
  (except `antisymmetrization`, maybe it could be transferred)
* `is_total_preorder`, `is_partial_order`: unused except for instances
* `is_linear_order`: unused except for instances
* `is_equiv`: unused except for instances (most uses can use `equivalence` instead)
* `is_per`: unused
* `is_incomp_trans`: unused
* `is_strict_weak_order`: significant usage (most of it on `rbmap`, could be transferred)
* `is_trichotomous`: some usage
* `is_strict_total_order`: looks like the only usage is in `rbmap` again
-/

universe u v

-- Porting note: removed `outParam`
class IsSymmOp (α : Sort u) (β : Sort v) (op : α → α → β) : Prop where
  symm_op : ∀ a b, op a b = op b a

/-- A commutative binary operation. -/
@[deprecated Std.Commutative (since := "2024-02-02")]
abbrev IsCommutative (α : Sort u) (op : α → α → α) := Std.Commutative op

instance (priority := 100) isSymmOp_of_isCommutative (α : Sort u) (op : α → α → α)
    [Std.Commutative op] : IsSymmOp α α op where symm_op := Std.Commutative.comm

/-- An associative binary operation. -/
@[deprecated Std.Associative (since := "2024-02-02")]
abbrev IsAssociative (α : Sort u) (op : α → α → α) := Std.Associative op

/-- A binary operation with a left identity. -/
@[deprecated Std.LawfulLeftIdentity (since := "2024-02-02")]
abbrev IsLeftId (α : Sort u) (op : α → α → α) (o : outParam α) := Std.LawfulLeftIdentity op o

/-- A binary operation with a right identity. -/
@[deprecated Std.LawfulRightIdentity (since := "2024-02-02")]
abbrev IsRightId (α : Sort u) (op : α → α → α) (o : outParam α) := Std.LawfulRightIdentity op o

class IsLeftCancel (α : Sort u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c

class IsRightCancel (α : Sort u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c

@[deprecated Std.IdempotentOp (since := "2024-02-02")]
abbrev IsIdempotent (α : Sort u) (op : α → α → α) := Std.IdempotentOp op

/-- The opposite of a symmetric relation is symmetric. -/
instance (priority := 100) isSymmOp_of_isSymm (α : Sort u) (r : α → α → Prop) [IsSymm α r] :
    IsSymmOp α Prop r where symm_op a b := propext <| Iff.intro (IsSymm.symm a b) (IsSymm.symm b a)
