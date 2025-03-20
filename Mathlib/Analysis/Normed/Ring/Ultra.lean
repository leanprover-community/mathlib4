/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Ultrametric norms on rings where the norm of one is one

This file contains results on the behavior of norms in ultrametric normed rings.
The norm must send one to one.

## Main results

* `norm_intCast_le_one`:
  the norm of the image of an integer in the ring is always less than or equal to one

## Implementation details

A `[NormedRing R]` only assumes a submultiplicative norm and does not have `[NormOneClass R]`.
The weakest ring-like structure that has a bundled norm such that `‖1‖ = 1` is
`[NormedDivisionRing K]`.
Since the statements below hold in any context, we can state them
in an unbundled fashion using `[NormOneClass R]`.
In fact one can actually prove all these lemmas only assuming
`{R : Type*} [SeminormedAddGroup R] [One R] [NormOneClass R] [IsUltrametricDist R]`.
But one has to give the typeclass machinery a little help in order to get it to recognise that there
is a coercion from `ℕ` or `ℤ` to `R`.
Instead, we use weakest pre-existing typeclass that implies both
`[SeminormedAddGroup R]` and `[AddGroupWithOne R]`, which is `[SeminormedRing R]`.

## Tags

ultrametric, nonarchimedean
-/
open Metric NNReal

namespace IsUltrametricDist

section NormOneClass

variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

lemma norm_add_one_le_max_norm_one (x : R) :
    ‖x + 1‖ ≤ max ‖x‖ 1 := by
  simpa only [le_max_iff, norm_one] using norm_add_le_max x 1

lemma nnnorm_add_one_le_max_nnnorm_one (x : R) :
    ‖x + 1‖₊ ≤ max ‖x‖₊ 1 :=
  norm_add_one_le_max_norm_one _

variable (R)
lemma nnnorm_natCast_le_one (n : ℕ) :
    ‖(n : R)‖₊ ≤ 1 := by
  induction n with
  | zero => simp only [Nat.cast_zero, nnnorm_zero, zero_le]
  | succ n hn => simpa only [Nat.cast_add, Nat.cast_one, hn, max_eq_right] using
    nnnorm_add_one_le_max_nnnorm_one (n : R)

lemma norm_natCast_le_one (n : ℕ) :
    ‖(n : R)‖ ≤ 1 :=
  nnnorm_natCast_le_one R n

lemma nnnorm_intCast_le_one (z : ℤ) :
    ‖(z : R)‖₊ ≤ 1 := by
  cases z <;>
  simpa only [Int.ofNat_eq_coe, Int.cast_natCast, Int.cast_negSucc, Nat.cast_one, nnnorm_neg]
    using nnnorm_natCast_le_one _ _

lemma norm_intCast_le_one (z : ℤ) :
    ‖(z : R)‖ ≤ 1 :=
  nnnorm_intCast_le_one _ z

end NormOneClass

end IsUltrametricDist
