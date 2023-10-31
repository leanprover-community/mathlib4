/-
Copyright (c) 2023 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Miguel Marco
-/
import Init.Data.Nat.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Tactic.FieldSimp
import Std.Data.Nat.Lemmas

open Lean Meta Elab Tactic Parser Tactic

/-!
# `unify_denoms` and `unify_denoms!` tactics

Tactics to clear denominators in algebraic expressions, extends `field_simp`  using
rules that require denominators to be nonzero. The corresponding hypotheses are
added as new goals.

The `unify_denoms` tactic tries to unify denominators in expressions, adding the
necessary hypothesis about denominators being nonzero (and dividing the numerator in the case
of euclidean domains) as new goals.

The `unify_denoms!` tactic extends `unify_denoms` to work also on
(in)equalities. In the case of inequalities, it assumes denominators are positive.
--/

/-
The following lemmas are needed to manage divisions in the naturals:
-/

/--
`unify_denoms` reduces expressions with nested fractions to a single fraction.

It adds the hypothesis that the corresponding denominators are nonzero (and divide the numerator
in the case of euclidean domains) as new goals.
-/
syntax (name := unify_denoms) "unify_denoms" (location)? : tactic

macro_rules
| `(tactic | unify_denoms $[at $location]?) => `(tactic |(
  try field_simp $[at $location]?
  repeat (first
  | (rw [← one_div]         $[at $location]?)
  | (rw [div_add_div]       $[at $location]?)
  | (rw [div_sub_div]       $[at $location]?)
  | (rw [add_div']          $[at $location]?)
  | (rw [div_add']          $[at $location]?)
  | (rw [div_sub']          $[at $location]?)
  | (rw [sub_div']          $[at $location]?)
  | (rw [mul_div_mul_right] $[at $location]?)
  | (rw [mul_div_mul_left]  $[at $location]?)
  | (rw [Nat.div_div_eq_div_mul]  $[at $location]?)
  | (rw [Nat.div_self]                             $[at $location]?)
  | (rw [Nat.mul_div_mul_right]                    $[at $location]?)
  | (rw [Nat.mul_div_mul_left]                     $[at $location]?)
  | (rw [Nat.div_add_div_of_dvd]                   $[at $location]?)
  | (rw [Nat.div_sub_div_of_dvd]                   $[at $location]?)
  | (rw [Nat.div_add_of_dvd]                       $[at $location]?)
  | (rw [Nat.div_sub_of_dvd]                       $[at $location]?)
  | (rw [Nat.add_div_of_dvd]                       $[at $location]?)
  | (rw [Nat.sub_div_of_dvd]                       $[at $location]?)
  | (rw [EuclideanDomain.mul_div_cancel]           $[at $location]?)
  | (rw [EuclideanDomain.mul_div_cancel']          $[at $location]?)
  | (rw [EuclideanDomain.mul_div_cancel_left]      $[at $location]?)
  | (rw [EuclideanDomain.mul_div_mul_cancel]       $[at $location]?)
  | (rw [←EuclideanDomain.mul_div_assoc]           $[at $location]?)
  | (rw [EuclideanDomain.div_div]                  $[at $location]?)
  | (rw [EuclideanDomain.div_add_of_dvd]           $[at $location]?)
  | (rw [EuclideanDomain.div_sub_of_dvd]           $[at $location]?)
  | (rw [EuclideanDomain.add_div_of_dvd]           $[at $location]?)
  | (rw [EuclideanDomain.sub_div_of_dvd]           $[at $location]?)
  | (rw [EuclideanDomain.div_add_div_of_dvd]       $[at $location]?)
  | (rw [EuclideanDomain.div_sub_div_of_dvd]       $[at $location]?)
  | (rw [←Nat.mul_div_assoc]                       $[at $location]?)
  | (rw [Nat.div_mul_assoc]                        $[at $location]?)
  | (rw [Nat.div_mul_div_comm]                     $[at $location]?)
   )))

/--
`unify_denoms!` works as `unify_denoms`, but:
- it also simplifies divisions in euclidean domains, and
- it also tries to cancel denominators in both sides of an (in)equality.

The needed hypothesis about the divisibility and sign of denominators are added as new goals.
-/
syntax (name := unify_denoms!) "unify_denoms!" (location)?: tactic

macro_rules
| `(tactic | unify_denoms! $[at $location]?) => `(tactic |(
  unify_denoms $[at $location]?
  repeat (first
  | (rw [mul_eq_zero]                              $[at $location]?)
  | (rw [eq_comm,mul_eq_zero]                      $[at $location]?)
  | (rw [div_eq_zero_iff]                          $[at $location]?)
  | (rw [div_eq_div_iff]                           $[at $location]?)
  | (rw [gt_iff_lt]                                $[at $location]?)
  | (rw [ge_iff_le]                                $[at $location]?)
  | (rw [div_le_div_iff]                           $[at $location]?)
  | (rw [div_lt_div_iff]                           $[at $location]?)
  | (rw [div_eq_iff]                               $[at $location]?)
  | (rw [div_le_iff]                               $[at $location]?)
  | (rw [div_lt_iff]                               $[at $location]?)
  | (rw [eq_div_iff]                               $[at $location]?)
  | (rw [le_div_iff]                               $[at $location]?)
  | (rw [lt_div_iff]                               $[at $location]?)
  | (rw [lt_div_iff]                               $[at $location]?)
  | (rw [Nat.div_eq_iff_eq_mul_left]               $[at $location]?)
  | (rw [Nat.eq_div_iff_mul_eq_left]               $[at $location]?)
  | (rw [eq_comm,Nat.div_eq_iff_eq_mul_left]       $[at $location]?)
  | (rw [Nat.div_lt_iff_lt_mul]                    $[at $location]?)
  | (rw [Nat.le_div_iff_mul_le]                    $[at $location]?)
  | (rw [Nat.div_le_iff_le_mul_of_dvd]             $[at $location]?)
  | (rw [Nat.lt_div_iff_mul_lt_of_dvd]             $[at $location]?)
  | (rw [EuclideanDomain.div_eq_div_iff_mul_eq_mul_of_dvd] $[at $location]?)
  | (rw [EuclideanDomain.eq_div_iff_mul_eq_of_dvd]         $[at $location]?)
  | (rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd]         $[at $location]?)
  | (push_neg                                      $[at $location]?) )
  try (any_goals assumption) ))
