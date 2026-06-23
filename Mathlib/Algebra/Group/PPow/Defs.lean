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

variable {M : Type*}

instance Semigroup.instPow [Semigroup M] : Pow M ℕ+ where
  pow x n := Semigroup.ppow n n.property x

instance AddSemigroup.instSMul [AddSemigroup M] : SMul ℕ+ M where
  smul n x := AddSemigroup.psmul n n.property x

attribute [to_additive existing AddSemigroup.instSMul] Semigroup.instPow

@[to_additive (attr := simp)]
lemma Semigroup.ppow_eq_pow [Semigroup M] (x : M) (n : ℕ+) :
    Semigroup.ppow n n.property x = x ^ n :=
  rfl

@[simp]
lemma one_psmul [AddSemigroup M] (x : M) : (1 : ℕ+) • x = x :=
  AddSemigroup.psmul_one _

@[to_additive (attr := simp) existing]
lemma ppow_one [Semigroup M] (x : M) : x ^ (1 : ℕ+) = x :=
  Semigroup.ppow_one _

@[to_additive]
lemma ppow_mk_add_one [Semigroup M] (x : M) {n : ℕ} (hn : n ≠ 0) :
    x ^ (PNat.mk (n + 1) (Nat.succ_pos n)) = x * x ^ (PNat.mk n (Nat.pos_of_ne_zero hn)) := by
  cases n
  · contradiction
  · simp [← Semigroup.ppow_eq_pow, PNat.mk, Semigroup.ppow_succ]

-- not marked as `simp` because in a monoid we probably prefer powers with type `ℕ`
@[to_additive (attr := norm_cast)]
theorem npow_val_eq_ppow [Monoid M] (n : ℕ+) (x : M) : x ^ n.val = x ^ n := by
  rcases n with ⟨_|n, hn⟩
  · contradiction
  simp only [mk_coe, ← Semigroup.ppow_eq_pow]
  induction n
  · simp [Semigroup.ppow_one]
  · simp_all [Semigroup.ppow_succ, pow_succ']

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy
@[to_additive (attr := simp high) psmul_zero] lemma one_ppow [Monoid M] (n : ℕ+) :
    (1 : M) ^ n = 1 := by
  rw [← npow_val_eq_ppow, one_pow]

section CommSemigroup

variable [CommSemigroup M]

@[to_additive psmul_add]
lemma mul_ppow (x y : M) (n : ℕ+) : (x * y) ^ n = x ^ n * y ^ n := by
  rcases n with ⟨_|n, hn⟩
  · contradiction
  simp only [mk_coe, ← Semigroup.ppow_eq_pow]
  induction n with
  | zero => simp [Semigroup.ppow_one]
  | succ n IH =>
    rw [Semigroup.ppow_succ, IH (Nat.succ_pos _), Semigroup.ppow_succ, Semigroup.ppow_succ,
        mul_assoc, mul_comm y, ← mul_assoc, ← mul_assoc, mul_comm y, ← mul_assoc]

end CommSemigroup
