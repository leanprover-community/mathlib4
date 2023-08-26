/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

#align_import group_theory.commuting_probability from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/

set_option autoImplicit true

noncomputable section

open Classical

open BigOperators

open Fintype

variable (M : Type*) [Mul M]

/-- The commuting probability of a finite type with a multiplication operation. -/
def commProb : ℚ :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2
#align comm_prob commProb

theorem commProb_def :
    commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2 :=
  rfl
#align comm_prob_def commProb_def

theorem commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ←Nat.cast_mul,
    ←Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_pi (i : α → Type*) [Fintype α] [∀ a, Mul (i a)] :
    commProb (∀ a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ←Nat.cast_prod,
    ←Nat.card_pi, Commute, SemiconjBy, Function.funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_function [Fintype α] [Mul β] :
    commProb (α → β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi, Finset.prod_const, Finset.card_univ]

@[simp]
theorem commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0 :=
  div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

variable [Finite M]

theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x ↦
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)
#align comm_prob_pos commProb_pos

theorem commProb_le_one : commProb M ≤ 1 := by
  refine' div_le_one_of_le _ (sq_nonneg (Nat.card M : ℚ))
  rw [← Nat.cast_pow, Nat.cast_le, sq, ← Nat.card_prod]
  apply Finite.card_subtype_le
#align comm_prob_le_one commProb_le_one

variable {M}

theorem commProb_eq_one_iff [h : Nonempty M] :
    commProb M = 1 ↔ Commutative ((· * ·) : M → M → M) := by
  haveI := Fintype.ofFinite M
  rw [commProb, ← Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod,
    set_fintype_card_eq_univ_iff, Set.eq_univ_iff_forall]
  · exact ⟨fun h x y ↦ h (x, y), fun h x ↦ h x.1 x.2⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)
#align comm_prob_eq_one_iff commProb_eq_one_iff

variable (G : Type*) [Group G]

theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  by_cases h : (Nat.card G : ℚ) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h
#align comm_prob_def' commProb_def'

variable {G}
variable [Finite G] (H : Subgroup G)

theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * (H.index : ℚ) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · refine' Finite.card_le_of_injective (fun p ↦ ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) _
    exact fun p q h ↦ by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2
#align subgroup.comm_prob_subgroup_le Subgroup.commProb_subgroup_le

theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · apply Finite.card_le_of_surjective
    show Function.Surjective (ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.surjective_Quotient_mk''
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos
#align subgroup.comm_prob_quotient_le Subgroup.commProb_quotient_le

variable (G)

theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_pos_le_iff_one_le_mul (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).mul_comm))
      (commutator G).commProb_quotient_le)
#align inv_card_commutator_le_comm_prob inv_card_commutator_le_commProb
