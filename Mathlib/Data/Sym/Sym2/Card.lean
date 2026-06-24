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
  simp [mk_fiber]

theorem ncard_mk_fiber_of_isDiag {z : Sym2 α} (hz : z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 1 := by
  cases z
  cases hz
  simp [mk_fiber]

theorem ncard_mk_fiber_of_not_isDiag {z : Sym2 α} (hz : ¬z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 2 := by
  cases z
  simp [mk_fiber, mk_isDiag_iff.not.mp hz]

theorem ncard_mk_fiber [DecidableEq α] (z : Sym2 α) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = if z.IsDiag then 1 else 2 := by
  split_ifs with h
  · rw [ncard_mk_fiber_of_isDiag h]
  · rw [ncard_mk_fiber_of_not_isDiag h]

theorem ncard_mk_fiber_eq_card_toFinset [DecidableEq α] {z : Sym2 α} :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = z.toFinset.card := by
  rw [ncard_mk_fiber, card_toFinset]

theorem encard_mk_fiber_le (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).encard ≤ 2 := by
  classical
  rw [← z.finite_mk_fiber.cast_ncard_eq, z.ncard_mk_fiber]
  split_ifs <;> norm_cast

variable (α) in
theorem two_mul_cardinalMk_sym2 : 2 * #(Sym2 α) = #α * (#α + 1) := by
  classical
  have : Bool × Sym2 α ≃ α × Option α := {
    toFun
      | ⟨true, z⟩ => (z.out.fst, some z.out.snd)
      | ⟨false, z⟩ => (z.out.snd, if z.IsDiag then none else some z.out.fst)
    invFun
      | ⟨a, some b⟩ => (s(a, b).out.fst = a, s(a, b))
      | ⟨a, none⟩ => (false, s(a, a))
    left_inv := by grind [mk_fst_out_snd_out, mk_isDiag_iff]
    right_inv _ := by grind [mk_fst_out_snd_out, mk_isDiag_iff]
  }
  simpa using this.cardinal_eq

variable (α) in
theorem cardinalMk_prod_le : #(α × α) ≤ 2 * #(Sym2 α) := by
  simp [two_mul_cardinalMk_sym2, mul_le_mul_right]

section fromRel

variable {r : α → α → Prop} (sym : Std.Symm r)

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm]
  grw [Cardinal.sum_le_mk_mul_iSup]
  apply mul_le_mul_right <| ciSup_le' fun z ↦ ?_
  rw [← Set.coe_setOf, ← Set.preimage_singleton]
  rcases z with ⟨⟨⟩⟩
  grw [mk_fiber, ← Set.cast_ncard, Set.ncard_insert_le] <;>
    simp

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm, ← Cardinal.sum_const']
  congr
  ext ⟨z, hz⟩
  rw [← Set.coe_setOf, ← Set.preimage_singleton, ← Set.cast_ncard z.finite_mk_fiber,
    z.ncard_mk_fiber_of_not_isDiag, Nat.cast_two]
  exact fromRel_irrefl.mp ‹_› hz

end fromRel

end Sym2
