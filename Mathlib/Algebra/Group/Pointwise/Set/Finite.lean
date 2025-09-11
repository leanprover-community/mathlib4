/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

assert_not_exists MulAction MonoidWithZero

open Pointwise

variable {F α β γ : Type*}

namespace Set

section One

variable [One α]

@[to_additive (attr := simp)]
theorem finite_one : (1 : Set α).Finite :=
  finite_singleton _

end One

section Mul

variable [Mul α] {s t : Set α}

@[to_additive]
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive /-- Addition preserves finiteness. -/]
instance fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t) :=
  Set.fintypeImage2 _ _ _

end Mul

section Monoid

variable [Monoid α] {s t : Set α}

@[to_additive]
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ s * t) := fun _ ↦ decidable_of_iff _ mem_mul.symm

@[to_additive]
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
    DecidablePred (· ∈ s ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, mem_one]
    infer_instance
  | succ n ih =>
    letI := ih
    rw [pow_succ]
    infer_instance

end Monoid

section SMul

variable [SMul α β] {s : Set α} {t : Set β}

@[to_additive]
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _

end SMul

section HasSMulSet

variable [SMul α β] {s : Set β} {a : α}

@[to_additive]
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _

@[to_additive]
theorem Infinite.of_smul_set : (a • s).Infinite → s.Infinite :=
  Infinite.of_image _

end HasSMulSet

section Vsub

variable [VSub α β] {s t : Set β}

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht

end Vsub

section Cancel

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
lemma finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ ↦ (mul_left_injective _).injOn) fun _ _ ↦ (mul_right_injective _).injOn

@[to_additive]
lemma infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

end Cancel

section InvolutiveInv
variable [InvolutiveInv α] {s : Set α}

@[to_additive (attr := simp)] lemma finite_inv : s⁻¹.Finite ↔ s.Finite := by
  rw [← image_inv_eq_inv, finite_image_iff inv_injective.injOn]

@[to_additive (attr := simp)] lemma infinite_inv : s⁻¹.Infinite ↔ s.Infinite := finite_inv.not

@[to_additive] alias ⟨Finite.of_inv, Finite.inv⟩ := finite_inv

end InvolutiveInv

section Div
variable [Div α] {s t : Set α}

@[to_additive] lemma Finite.div : s.Finite → t.Finite → (s / t).Finite := .image2 _

/-- Division preserves finiteness. -/
@[to_additive /-- Subtraction preserves finiteness. -/]
instance fintypeDiv [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s / t) :=
  Set.fintypeImage2 _ _ _

end Div

section Group

variable [Group α] {s t : Set α}

@[to_additive]
lemma finite_div : (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

@[to_additive]
lemma infinite_div : (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ ↦ div_left_injective.injOn) fun _ _ ↦ div_right_injective.injOn

end Group

end Set

open Set

namespace Group

variable {G : Type*} [Group G] [Fintype G] (S : Set G)

@[to_additive]
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card (↥(S ^ k)) = Fintype.card (↥(S ^ Fintype.card G)) := by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with (rfl | ⟨a, ha⟩)
  · refine fun k hk ↦ Fintype.card_congr ?_
    rw [empty_pow (hG.trans_le hk).ne', empty_pow (ne_of_gt hG)]
  have key : ∀ (a) (s t : Set G) [Fintype s] [Fintype t],
      (∀ b : G, b ∈ s → b * a ∈ t) → Fintype.card s ≤ Fintype.card t := by
    refine fun a s t _ _ h ↦ Fintype.card_le_of_injective (fun ⟨b, hb⟩ ↦ ⟨b * a, h b hb⟩) ?_
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_right_cancel (Subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n ↦ Fintype.card (↥(S ^ n)) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n ↦ key a _ _ fun b hb ↦ Set.mul_mem_mul hb ha
  refine fun _ ↦ Nat.stabilises_of_monotone mono (fun n ↦ set_fintype_card_le_univ (S ^ n))
    fun n h ↦ le_antisymm (mono (n + 1).le_succ) (key a⁻¹ (S ^ (n + 2)) (S ^ (n + 1)) ?_)
  replace h₂ : S ^ n * {a} = S ^ (n + 1) := by
    have : Fintype (S ^ n * Set.singleton a) := by
      classical
      apply fintypeMul
    refine Set.eq_of_subset_of_card_le ?_ (le_trans (ge_of_eq h) ?_)
    · exact mul_subset_mul Set.Subset.rfl (Set.singleton_subset_iff.mpr ha)
    · convert key a (S ^ n) (S ^ n * {a}) fun b hb ↦ Set.mul_mem_mul hb (Set.mem_singleton a)
  rw [pow_succ', ← h₂, ← mul_assoc, ← pow_succ', h₂, mul_singleton, forall_mem_image]
  intro x hx
  rwa [mul_inv_cancel_right]

end Group
