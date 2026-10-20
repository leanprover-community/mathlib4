/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.PNat.Notation

/-!
# Instances for `ℕ+`-indexed powers on semigroups

Declared in a separate file to bootstrap the algebra hierarchy without
requiring instances on `ℕ+`, which are usually inferred via inheriting from `ℕ`.
-/

public section

open PNat

variable {M : Type*}

@[to_additive (attr := elab_as_elim)]
lemma Semigroup.ppow_induction [Semigroup M] {p : ℕ+ → M → Prop} (x : M) (n : ℕ+)
    (h1 : p 1 x) (hsucc : ∀ n : ℕ+, p n (x ^ n) → p (n + 1) (x ^ n * x)) :
    p n (x ^ n) := by
  induction n
  · simpa
  · grind [ppow_succ]

@[to_additive psmul_mk_add_one]
lemma ppow_mk_add_one [Semigroup M] (x : M) {n : ℕ} (hn : n ≠ 0 := by exact Nat.succ_ne_zero _) :
    x ^ (PNat.mk (n + 1) (Nat.succ_pos n)) = x ^ (PNat.mk n (Nat.pos_of_ne_zero hn)) * x :=
  ppow_succ x (mk n _)

@[to_additive psmul_mk_add_one']
lemma ppow_mk_add_one' [Semigroup M] (x : M) {n : ℕ} (hn : n ≠ 0 := by exact Nat.succ_ne_zero _) :
    x ^ (PNat.mk (n + 1) (Nat.succ_pos n)) = x * x ^ (PNat.mk n (Nat.pos_of_ne_zero hn)) :=
  ppow_succ' x (mk n _)

@[to_additive (attr := elab_as_elim)]
lemma Semigroup.ppow_induction' [Semigroup M] {p : ℕ+ → M → Prop} (x : M) (n : ℕ+)
    (h1 : p 1 x) (hsucc : ∀ n : ℕ+, p n (x ^ n) → p (n + 1) (x * x ^ n)) :
    p n (x ^ n) := by
  induction n
  · simpa
  · grind [ppow_succ']

-- not marked as `simp` because in a monoid we probably prefer powers with type `ℕ`
@[to_additive (attr := norm_cast)]
theorem npow_val_eq_ppow [Monoid M] (n : ℕ+) (x : M) : x ^ n.val = x ^ n := by
  induction n using Semigroup.ppow_induction x with
  | h1 => simp
  | hsucc n IH => simp [pow_succ, IH]

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy
@[to_additive (attr := simp high) psmul_zero] lemma one_ppow [Monoid M] (n : ℕ+) :
    (1 : M) ^ n = 1 := by
  rw [← npow_val_eq_ppow, one_pow]

section CommSemigroup

variable [CommSemigroup M]

@[to_additive psmul_add]
lemma mul_ppow (x y : M) (n : ℕ+) : (x * y) ^ n = x ^ n * y ^ n := by
  induction n using Semigroup.ppow_induction (x * y) with
  | h1 => simp
  | hsucc n IH =>
    rw [ppow_succ x, ppow_succ y, IH, ← mul_assoc, mul_assoc _ _ x, mul_comm _ x,
        ← mul_assoc, ← mul_assoc]

end CommSemigroup
