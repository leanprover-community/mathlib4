/-
Copyright (c) 2025 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Nat.Cast.Order.Ring


/-!
# `norm_num` plugin for `abs`

TODO: plugins for `mabs`, `norm`, `nnorm`, and `enorm`.
-/

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

theorem isNat_abs_nonneg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : ℕ} (pa : IsNat a na) : IsNat |a| na := by
  rw [pa.out, Nat.abs_cast]
  constructor
  rfl

theorem isNat_abs_neg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : ℕ} (pa : IsInt a (.negOfNat na)) : IsNat |a| na := by
  rw [pa.out]
  constructor
  simp

theorem isNNRat_abs_nonneg {α : Type*} [DivisionRing α] [LinearOrder α]
    [IsStrictOrderedRing α] {a : α} {num den : ℕ} (ra : IsNNRat a num den) :
    IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

theorem isNNRat_abs_neg {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {num den : ℕ} (ra : IsRat a (.negOfNat num) den) : IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  simp only [Int.cast_negOfNat, neg_mul, abs_neg]
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

/-- The `norm_num` extension which identifies expressions of the form `|a|`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num |_|] def evalAbs : NormNumExt where eval {u α}
  | ~q(@abs _ $instLattice $instAddGroup $a) => do
    match ← derive a with
    | .isBool ..  => failure
    | .isNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat sα na q(isNat_abs_nonneg $pa)
    | .isNegNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat _ _ q(isNat_abs_neg $pa)
    | .isNNRat dsα' qe' nume' dene' pe' =>
      let rα : Q(DivisionRing $α) ← synthInstanceQ q(DivisionRing $α)
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ qe' _ _ q(isNNRat_abs_nonneg $pe')
    | .isNegNNRat dα' qe' nume' dene' pe' =>
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ (-qe') _ _ q(isNNRat_abs_neg $pe')

end Mathlib.Meta.NormNum
