/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Torsion group of `ZMod p` for prime `p`

This file shows that the `ZMod p` has `p - 1` roots-of-unity.

-/

@[expose] public section

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
