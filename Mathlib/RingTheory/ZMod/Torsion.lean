/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.FieldTheory.Finite.Basic

/-!
# Torsion group of `ZMod p` for prime `p`

This file shows that the `ZMod p` has `p - 1` roots-of-unity.

-/

namespace ZMod

lemma rootsOfUnity_eq_top {p : ℕ} [Fact p.Prime] :
    (rootsOfUnity (p - 1) (ZMod p)) = ⊤ := by
  ext
  simpa [Units.ext_iff] using pow_card_sub_one_eq_one (Units.ne_zero _)

instance {p : ℕ} [Fact p.Prime] : HasEnoughRootsOfUnity (ZMod p) (p - 1) := by
  have : NeZero (p - 1) := ⟨by have : 2 ≤ p := Nat.Prime.two_le Fact.out; grind⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have := Nat.card_congr (MulEquiv.subgroupCongr (ZMod.rootsOfUnity_eq_top (p := p))).toEquiv
  rw [Nat.card_eq_fintype_card] at this
  rw [this]
  simp [Fintype.card_units]

end ZMod
