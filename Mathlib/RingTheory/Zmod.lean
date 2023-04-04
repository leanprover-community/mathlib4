/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module ring_theory.zmod
! leanprover-community/mathlib commit 00d163e35035c3577c1c79fa53b68de17781ffc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Squarefree
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.Int.Basic

/-!
# Ring theoretic facts about `zmod n`

We collect a few facts about `zmod n` that need some ring theory to be proved/stated

## Main statements

* `is_reduced_zmod` - `zmod n` is reduced for all squarefree `n`.
-/


@[simp]
theorem isReduced_zMod {n : ℕ} : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0 := by
  rw [←
    RingHom.ker_isRadical_iff_reduced_of_surjective
      (ZMod.ringHom_surjective <| Int.castRingHom <| ZMod n),
    ZMod.ker_int_castRingHom, ← isRadical_iff_span_singleton, isRadical_iff_squarefree_or_zero,
    Int.squarefree_coe_nat, Nat.cast_eq_zero]
#align is_reduced_zmod isReduced_zMod

instance {n : ℕ} [Fact <| Squarefree n] : IsReduced (ZMod n) :=
  isReduced_zMod.2 <| Or.inl <| Fact.out _

