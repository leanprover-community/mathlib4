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

@[to_additive (attr := elab_as_elim)]
lemma Semigroup.ppow_induction [Semigroup M] {p : ℕ+ → M → Prop} (x : M) (n : ℕ+)
    (h1 : p 1 x) (hsucc : ∀ n : ℕ,
    p (PNat.mk (n + 1) (Nat.succ_pos n)) (x ^ PNat.mk (n + 1) (Nat.succ_pos n)) →
    p (PNat.mk (n + 2) (Nat.succ_pos (n + 1)))
      (x ^ PNat.mk (n + 1) (Nat.succ_pos n) * x)) :
    p n (x ^ n) := by
  rcases n with ⟨n, hn⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  let q : ℕ → Prop := fun k =>
    p (PNat.mk (k + 1) (Nat.succ_pos k)) (x ^ PNat.mk (k + 1) (Nat.succ_pos k))
  have hq (k : ℕ) : q k := by
    induction k with
    | zero => simpa [q, PNat.mk] using h1
    | succ k IH =>
      simpa [q, PNat.mk, ← Semigroup.ppow_eq_pow, Semigroup.ppow_succ] using hsucc k IH
  simpa [q, PNat.mk] using hq k

@[to_additive]
lemma ppow_mk_add_one [Semigroup M] (x : M) {n : ℕ} (hn : n ≠ 0 := by exact Nat.succ_ne_zero _) :
    x ^ (PNat.mk (n + 1) (Nat.succ_pos n)) = x ^ (PNat.mk n (Nat.pos_of_ne_zero hn)) * x := by
  cases n
  · contradiction
  · simp [← Semigroup.ppow_eq_pow, PNat.mk, Semigroup.ppow_succ]

@[to_additive]
lemma ppow_mk_add_one' [Semigroup M] (x : M) {n : ℕ} (hn : n ≠ 0 := by exact Nat.succ_ne_zero _) :
    x ^ (PNat.mk (n + 1) (Nat.succ_pos n)) = x * x ^ (PNat.mk n (Nat.pos_of_ne_zero hn)) := by
  cases n
  · contradiction
  · simp [← Semigroup.ppow_eq_pow, PNat.mk, Semigroup.ppow_succ']

@[to_additive (attr := elab_as_elim)]
lemma Semigroup.ppow_induction' [Semigroup M] {p : ℕ+ → M → Prop} (x : M) (n : ℕ+)
    (h1 : p 1 x) (hsucc : ∀ n : ℕ,
    p (PNat.mk (n + 1) (Nat.succ_pos n)) (x ^ PNat.mk (n + 1) (Nat.succ_pos n)) →
    p (PNat.mk (n + 2) (Nat.succ_pos (n + 1)))
      (x * x ^ PNat.mk (n + 1) (Nat.succ_pos n))) :
    p n (x ^ n) := by
  induction n using Semigroup.ppow_induction x
  · exact h1
  · rw [← ppow_mk_add_one, ppow_mk_add_one']
    exact hsucc _ ‹_›

-- not marked as `simp` because in a monoid we probably prefer powers with type `ℕ`
@[to_additive (attr := norm_cast)]
theorem npow_val_eq_ppow [Monoid M] (n : ℕ+) (x : M) : x ^ n.val = x ^ n := by
  induction n using Semigroup.ppow_induction x with
  | h1 => simp
  | hsucc n IH =>
    simp only [mk_coe] at IH
    simp [pow_succ _ (n + 1), IH]

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
    rw [ppow_mk_add_one x, ppow_mk_add_one y, IH, ← mul_assoc, mul_assoc _ _ x, mul_comm _ x,
        ← mul_assoc, ← mul_assoc]

end CommSemigroup
