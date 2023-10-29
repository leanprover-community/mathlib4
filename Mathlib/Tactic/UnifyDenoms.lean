/-
Copyright (c) 2023 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Miguel Marco
-/
import Init.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic Parser Tactic

/-!
# `unify_denoms` and `unify_denoms!` tactics

Tactics to clear denominators in algebraic expressions, extends `field_simp`  using
rules that require denominators to be nonzero. The corresponding hypotheses are
added as new goals.

The `unify_denoms` tactic tries to unify denominators in expressions, adding the
necessary hypothesis about denominators being nonzero as new goals.

The `unify_denoms!` tactic extends `unify_denoms` to work also on
(in)equalities.
--/

/--
`unify_denoms` reduces expressions with nested fractions to a single fraction.

It adds the hypothesis that the corresponding denominators are nonzero
as new goals.
-/
syntax (name := unify_denoms) "unify_denoms" (location)? : tactic


macro_rules
| `(tactic | unify_denoms $[at $location]?) => `(tactic |(
  field_simp $[at $location]?
  repeat (first
    | (rw [← one_div]         $[at $location]?)
    | (rw [div_add_div]       $[at $location]?)
    | (rw [div_sub_div]       $[at $location]?)
    | (rw [add_div']          $[at $location]?)
    | (rw [div_add']          $[at $location]?)
    | (rw [div_sub']          $[at $location]?)
    | (rw [sub_div']          $[at $location]?)
    | (rw [mul_div_mul_right] $[at $location]?)
    | (rw [mul_div_mul_left]  $[at $location]?) )))

/--
`unify_denoms!` works as `unify_denoms`, but also tries to cancel denominators
in both sides of an (in)equality.

For transforming inequalities between two fractions,
it uses the hypothesis the denominators are positive, and adds it as new goals.
-/
syntax (name := unify_denoms!) "unify_denoms!" (location)?: tactic

macro_rules
| `(tactic | unify_denoms! $[at $location]?) => `(tactic |(
  unify_denoms $[at $location]?
  repeat (first
  | (rw [mul_eq_zero]           $[at $location]?)
  | (rw [eq_comm,mul_eq_zero]   $[at $location]?)
  | (rw [div_eq_zero_iff]       $[at $location]?)
  | (rw [div_eq_div_iff]        $[at $location]?)
  | (rw [div_le_div_iff]        $[at $location]?)
  | (rw [div_lt_div_iff]        $[at $location]?)
  | (rw [div_eq_iff]            $[at $location]?)
  | (rw [div_le_iff]            $[at $location]?)
  | (rw [div_lt_iff]            $[at $location]?)
  | (rw [eq_div_iff]            $[at $location]?)
  | (rw [le_div_iff]            $[at $location]?)
  | (rw [lt_div_iff]            $[at $location]?)
  | (push_neg                   $[at $location]?)
   )))
