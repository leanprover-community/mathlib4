/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Algebra.SquareFree.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic

#align_import ring_theory.zmod from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Ring theoretic facts about `ZMod n`

We collect a few facts about `ZMod n` that need some ring theory to be proved/stated

## Main statements

* `isReduced_zmod` - `ZMod n` is reduced for all squarefree `n`.
-/


@[simp]
theorem isReduced_zmod {n : ℕ} : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0 := by
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective
      (ZMod.ringHom_surjective <| Int.castRingHom <| ZMod n),
      ZMod.ker_int_castRingHom, ← isRadical_iff_span_singleton, isRadical_iff_squarefree_or_zero,
      Int.squarefree_coe_nat, Nat.cast_eq_zero]
#align is_reduced_zmod isReduced_zmod

instance {n : ℕ} [Fact <| Squarefree n] : IsReduced (ZMod n) :=
  isReduced_zmod.2 <| Or.inl <| Fact.out
