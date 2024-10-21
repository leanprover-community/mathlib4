/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring


/-!
# Reversing tuples

This file provides the definition of the `reverse` function, which reverses a `Fin` tuple.

It also provides some lemmas about `reverse`, including the fact that it is involutive,
and how it interacts with other functions on tuples.

Rewrite lemmas tend to be oriented in the direction that pushes `reverse` to the right.

-/

universe u v

namespace Fin

variable {n : ℕ}

-- theorem rev_castSucc (k : Fin n) : rev (castSucc k) = succ (rev k)  := by
--   ext
--   simp only [val_succ, val_rev, coe_castSucc, Nat.succ_sub_succ_eq_sub]
--   zify [show k + 1 ≤ n from k.is_lt, show k ≤ n from is_le']
--   ring

-- theorem rev_succ (k : Fin n) : rev (succ k) = castSucc (rev k)  := by
--   ext
--   simp only [val_succ, val_rev, coe_castSucc, Nat.succ_sub_succ_eq_sub]

theorem rev_succ_rev (k : Fin n) : rev (succ (rev k)) = castSucc k := by
  simp [rev_succ]

/--
Reverses a tuple, turning the 0th entry into the n-1st, and so forth.
S
-/
def reverse {α : Fin n → Type u} (q : ∀ i, α i) : ∀ i : Fin n, α (rev i) :=
  fun i => q (rev i)

theorem init_eq_reverse_tail_reverse {α : Fin (n + 1) → Type u} (q : ∀ i, α i) (i) :
    init q i = _root_.cast (by rw [rev_succ_rev]) (reverse (tail (reverse (q))) i) := by
  unfold reverse
  rw [init, tail, eq_comm, cast_eq_iff_heq, rev_succ_rev]

theorem foo {α : Fin (n + 1) → Type u} :
    ((i : Fin n) → α i.rev.castSucc) = ((i : Fin n) → (α ∘ rev) i.succ) := by
  simp only [Function.comp_apply]
  simp_rw [rev_succ]


-- theorem castSucc_eq_reverse_succ_reverse {α : Fin n → Type u} (p : ∀ i, α i) (i) :
--     castSucc p i = _root_.cast (by rw [rev_succ_rev]) (reverse (succ (reverse p)) i) := by
--   unfold reverse
--   rw [castSucc, eq_comm, cast_eq_iff_heq, rev_succ_rev]

theorem snoc_eq_reverse_cons_reverse {α : Fin (n + 1) → Type u}
    (p : ∀ i : Fin n, α (castSucc i)) (x : α (last n)) :
    snoc p x = _root_.cast (_) (reverse (cons (α := α ∘ rev) (x) (_root_.cast (_) (reverse p)))) := by
  sorry
  --   snoc p x = _root_.cast (by rw [castSucc_eq_rev_succ_rev]) (reverse (cons x (reverse p))) := by
  -- sorry
  -- ext i
  -- rw [snoc, reverse, cons, cast_eq_iff_heq, castSucc_eq_rev_succ_rev]
  -- byCases h : i.val < n
  -- · rw [dif_pos h]
  --   exact congr_arg_heq p (Eq.refl (rev (succ (rev (castLT i h)))))
  -- · rw [dif_neg h]
  --   exact Eq.refl (rev (succ (rev (castLT i h))))


end Tuple
