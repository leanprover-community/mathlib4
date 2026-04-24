/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Sym2

/-!
# Cardinality of `Sym2`

This file compares the cardinalities of `Sym2 α` and `α × α` and related sets, such as the
equivalence class of a specific `z : Sym2 α`, or `Sym2.fromRel` sets.
-/

public section

namespace Sym2

open scoped Cardinal

variable {α : Type*}

/-- The equivalence class of an unordered pair -/
theorem mk_fiber (a b : α) : Sym2.mk.uncurry ⁻¹' {s(a, b)} = {(a, b), (b, a)} := by
  grind

theorem finite_mk_fiber (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).Finite := by
  cases z
  simp [Sym2.mk_fiber]

theorem ncard_mk_fiber_of_isDiag {z : Sym2 α} (hz : z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 1 := by
  cases z
  cases hz
  simp [Sym2.mk_fiber]

theorem ncard_mk_fiber_of_not_isDiag {z : Sym2 α} (hz : ¬z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 2 := by
  cases z
  simp [Sym2.mk_fiber, Sym2.mk_isDiag_iff.not.mp hz]

theorem ncard_mk_fiber [DecidableEq α] (z : Sym2 α) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = if z.IsDiag then 1 else 2 := by
  split_ifs with h
  · rw [Sym2.ncard_mk_fiber_of_isDiag h]
  · rw [Sym2.ncard_mk_fiber_of_not_isDiag h]

theorem ncard_mk_fiber_eq_card_toFinset [DecidableEq α] {z : Sym2 α} :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = z.toFinset.card := by
  rw [Sym2.ncard_mk_fiber, Sym2.card_toFinset]

theorem encard_mk_fiber_le (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).encard ≤ 2 := by
  classical
  rw [← z.finite_mk_fiber.cast_ncard_eq, z.ncard_mk_fiber]
  split_ifs <;> norm_cast

theorem cardinalMk_prod_le (α : Type*) : #(α × α) ≤ 2 * #(Sym2 α) := by
  rw [← Equiv.sigmaFiberEquiv Sym2.mk.uncurry |>.cardinal_eq, Cardinal.mk_sigma, mul_comm]
  grw [Cardinal.sum_le_mk_mul_iSup]
  apply mul_le_mul_right <| ciSup_le' fun z ↦ ?_
  rw [← Set.coe_setOf, ← Set.preimage_singleton]
  cases z
  grw [Sym2.mk_fiber, ← Set.cast_ncard, Set.ncard_insert_le] <;>
    simp

section fromRel

variable {r : α → α → Prop} (sym : Symmetric r)

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(Sym2.fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ Sym2.fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm]
  grw [Cardinal.sum_le_mk_mul_iSup]
  apply mul_le_mul_right <| ciSup_le' fun z ↦ ?_
  rw [← Set.coe_setOf, ← Set.preimage_singleton]
  rcases z with ⟨⟨⟩⟩
  grw [Sym2.mk_fiber, ← Set.cast_ncard, Set.ncard_insert_le] <;>
    simp

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel (irrefl : Std.Irrefl r) :
    #{ p : α × α // r p.fst p.snd } = 2 * #(Sym2.fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ Sym2.fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm, ← Cardinal.sum_const']
  congr
  ext ⟨z, hz⟩
  rw [← Set.coe_setOf, ← Set.preimage_singleton, ← Set.cast_ncard z.finite_mk_fiber,
    z.ncard_mk_fiber_of_not_isDiag, Nat.cast_two]
  exact Sym2.fromRel_irrefl.mp irrefl hz

end fromRel

end Sym2
