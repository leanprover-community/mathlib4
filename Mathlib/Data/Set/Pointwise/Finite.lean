/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Pointwise.SMul

#align_import data.set.pointwise.finite from "leanprover-community/mathlib"@"c941bb9426d62e266612b6d99e6c9fc93e7a1d07"

/-! # Finiteness lemmas for pointwise operations on sets -/


open Pointwise

variable {F α β γ : Type*}

namespace Set

section One

variable [One α]

@[to_additive (attr := simp)]
theorem finite_one : (1 : Set α).Finite :=
  finite_singleton _
#align set.finite_one Set.finite_one
#align set.finite_zero Set.finite_zero

end One

section InvolutiveInv

variable [InvolutiveInv α] {s : Set α}

@[to_additive]
theorem Finite.inv (hs : s.Finite) : s⁻¹.Finite :=
  hs.preimage inv_injective.injOn
#align set.finite.inv Set.Finite.inv
#align set.finite.neg Set.Finite.neg

end InvolutiveInv

section Mul

variable [Mul α] {s t : Set α}

@[to_additive]
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _
#align set.finite.mul Set.Finite.mul
#align set.finite.add Set.Finite.add

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t : Set α) :=
  Set.fintypeImage2 _ _ _
#align set.fintype_mul Set.fintypeMul
#align set.fintype_add Set.fintypeAdd

end Mul

section Monoid

variable [Monoid α] {s t : Set α}

@[to_additive]
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ s * t) := fun _ ↦ decidable_of_iff _ mem_mul.symm
#align set.decidable_mem_mul Set.decidableMemMul
#align set.decidable_mem_add Set.decidableMemAdd

@[to_additive]
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
    DecidablePred (· ∈ s ^ n) := by
  induction' n with n ih
  · simp only [Nat.zero_eq, pow_zero, mem_one]
    infer_instance
  · letI := ih
    rw [pow_succ]
    infer_instance
#align set.decidable_mem_pow Set.decidableMemPow
#align set.decidable_mem_nsmul Set.decidableMemNSMul

end Monoid

section SMul

variable [SMul α β] {s : Set α} {t : Set β}

@[to_additive]
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _
#align set.finite.smul Set.Finite.smul
#align set.finite.vadd Set.Finite.vadd

end SMul

section HasSMulSet

variable [SMul α β] {s : Set β} {a : α}

@[to_additive]
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _
#align set.finite.smul_set Set.Finite.smul_set
#align set.finite.vadd_set Set.Finite.vadd_set

@[to_additive]
theorem Infinite.of_smul_set : (a • s).Infinite → s.Infinite :=
  Infinite.of_image _
#align set.infinite.of_smul_set Set.Infinite.of_smul_set
#align set.infinite.of_vadd_set Set.Infinite.of_vadd_set

end HasSMulSet

section Vsub

variable [VSub α β] {s t : Set β}

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht
#align set.finite.vsub Set.Finite.vsub

end Vsub

section Cancel

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
theorem infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ =>
    (mul_right_injective _).injOn
#align set.infinite_mul Set.infinite_mul
#align set.infinite_add Set.infinite_add

@[to_additive]
lemma finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2  (fun _ _ ↦ (mul_left_injective _).injOn)
    fun _ _ ↦ (mul_right_injective _).injOn

end Cancel

section Group

variable [Group α] [MulAction α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
theorem finite_smul_set : (a • s).Finite ↔ s.Finite :=
  finite_image_iff (MulAction.injective _).injOn
#align set.finite_smul_set Set.finite_smul_set
#align set.finite_vadd_set Set.finite_vadd_set

@[to_additive (attr := simp)]
theorem infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn
#align set.infinite_smul_set Set.infinite_smul_set
#align set.infinite_vadd_set Set.infinite_vadd_set

alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
#align set.finite.of_smul_set Set.Finite.of_smul_set

alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set
#align set.infinite.smul_set Set.Infinite.smul_set

attribute [to_additive] Finite.of_smul_set Infinite.smul_set

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
  refine card_pow_eq_card_pow_card_univ_aux mono (fun n ↦ set_fintype_card_le_univ (S ^ n))
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
#align group.card_pow_eq_card_pow_card_univ Group.card_pow_eq_card_pow_card_univ
#align add_group.card_nsmul_eq_card_nsmul_card_univ AddGroup.card_nsmul_eq_card_nsmul_card_univ

end Group
