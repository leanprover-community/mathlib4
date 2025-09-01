/-
Copyright (c) 2025 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat


/-!
# `norm_num` plugin for `abs`
-/

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

theorem isNat_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {na : ℕ}
    (pa : IsNat a na) :
    IsNat |a| na := by
  rw [pa.out, Nat.abs_cast]
  constructor
  rfl

theorem isInt_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {na : ℕ}
    (pa : IsInt a (.negOfNat na)) :
    IsNat |a| na := by
  rw [pa.out]
  constructor
  simp

theorem isNNRat_abs {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {num den : ℕ}
    (ra : IsNNRat a num den) :
    IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, ?_⟩
  have : 0 ≤ ↑num * ⅟(den : α) := by
    apply mul_nonneg
    · exact Nat.cast_nonneg' num
    · simp_all only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]
  exact abs_of_nonneg this

/-- The `norm_num` extension which identifies expressions of the form `|a|`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num |_|] def evalAbs : NormNumExt where eval {u α} e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  match ra with
  | .isBool ..  => failure
  | .isNat sα na pa =>
    let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
    let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
    let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
    haveI' : $e =Q |$a| := ⟨⟩
    assumeInstancesCommute
    return .isNat sα na q(isNat_abs $pa)
  | .isNegNat sα na pa =>
    let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
    let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
    let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
    haveI' : $e =Q |$a| := ⟨⟩
    assumeInstancesCommute
    return .isNat q(«$rα».toAddGroupWithOne.toAddMonoidWithOne) _ q(isInt_abs $pa)
  | .isNNRat dsα' qe' nume' dene' pe' =>
    let rα : Q(DivisionRing $α) ← synthInstanceQ q(DivisionRing $α)
    let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
    let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
    haveI' : $e =Q |$a| := ⟨⟩
    assumeInstancesCommute
    return .isNNRat _ qe' _ _ q(isNNRat_abs $pe')
  | .isNegNNRat dα' qe' nume' dene' pe' => failure

end Mathlib.Meta.NormNum
