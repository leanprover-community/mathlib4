/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Properties of the `𝔤₂` Lie algebra.

Foo bar

## Main results:
 * `RootPairing.span_pair_eq_of_coxeterWeight_eq_three`: a finite crystallographic reduced
   irreducible root pairing containing two roots with Coxeter weight three is spanned by this pair.

-/

noncomputable section

open Function Set
open Submodule (span subset_span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [NoZeroSMulDivisors R M]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]

namespace RootPairing

variable {i j k : ι}
  -- (hg₂ : P.coxeterWeight i j = 3)
  (hg₂ : P.pairing i j = -3) -- `i` is long, `j` is short

include hg₂

lemma pairing_swap_eq :
    P.pairing j i = -1 := by
  suffices P.pairingIn ℤ j i = -1 by rw [← P.algebraMap_pairingIn ℤ, this]; simp
  have : P.pairingIn ℤ i j = -3 := by
    rw [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff, algebraMap_pairingIn]; simpa
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced i j
  aesop

lemma bar₁ : ∃ g : P.weylGroup, P.root j + P.root i = g • P.root j := by
  use ⟨Equiv.reflection P i, P.reflection_mem_weylGroup _⟩
  simp [reflection_apply_root, P.pairing_swap_eq hg₂]

lemma bar₂ : ∃ g : P.weylGroup, (2 : R) • P.root j + P.root i = g • P.root j := by
  use ⟨Equiv.reflection P j, P.reflection_mem_weylGroup _⟩ *
    ⟨Equiv.reflection P i, P.reflection_mem_weylGroup _⟩
  simp [← Equiv.root_indexEquiv_eq_smul, reflection_apply_root, hg₂, P.pairing_swap_eq hg₂]
  module

omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M] [P.IsCrystallographic]
  [P.IsReduced] in
lemma bar₃ : ∃ g : P.weylGroup, (3 : R) • P.root j + P.root i = g • P.root i := by
  use ⟨Equiv.reflection P j, P.reflection_mem_weylGroup _⟩
  simp [reflection_apply_root, hg₂, add_comm]

lemma bar₄ : ∃ g : P.weylGroup, (3 : R) • P.root j + (2 : R) • P.root i = g • P.root i := by
  use ⟨Equiv.reflection P i, P.reflection_mem_weylGroup _⟩ *
    ⟨Equiv.reflection P j, P.reflection_mem_weylGroup _⟩
  simp [← Equiv.root_indexEquiv_eq_smul, reflection_apply_root, hg₂, P.pairing_swap_eq hg₂]
  module

lemma length_ratio (B : P.InvariantForm) :
    B.form (P.root i) (P.root i) = 3 * B.form (P.root j) (P.root j) := by
  suffices P.pairing j i = -1 by simpa [hg₂, this] using B.pairing_mul_eq_pairing_mul_swap i j
  replace hg₂ : P.pairingIn ℤ i j = -3 := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, hg₂]
    simp
  suffices P.pairingIn ℤ j i = -1 by simp [← P.algebraMap_pairingIn ℤ, this]
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced i j
  aesop

lemma foo_short (B : P.InvariantForm)
    (hk : P.root k ∉ span R {P.root i, P.root j})
    (short : B.form (P.root k) (P.root k) = B.form (P.root j) (P.root j)) :
    P.IsOrthogonal k i ∧ P.IsOrthogonal k j := by
  suffices P.pairingIn ℤ k i = 0 ∧ P.pairingIn ℤ k j = 0 by
    simp only [← B.coxeterWeight_zero_iff_isOrthogonal, ← P.algebraMap_coxeterWeightIn ℤ]
    simp [coxeterWeightIn, this.1, this.2]

  have aux {l : ι} (hl : P.root l ∈ span R {P.root i, P.root j}) :
      k ≠ l ∧ P.root k ≠ - P.root l := by
    contrapose! hk
    rcases eq_or_ne k l with rfl | hkl; · assumption
    rw [hk hkl]
    exact neg_mem hl

  have hj : P.root j ∈ span R {P.root i, P.root j} := subset_span <| mem_insert_of_mem _ rfl
  have hb : P.pairingIn ℤ k j ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne short (aux hj).1 (aux hj).2
    simp at this ⊢
    omega

  obtain ⟨g, hg⟩ := P.bar₁ hg₂
  let l := P.weylGroupToPerm g j
  have hl₀ : P.root j + P.root i = P.root l := by rwa [weylGroup_apply_root] at hg
  have hl₁ : B.form (P.root k) (P.root k) = B.form (P.root l) (P.root l) := by
    rw [← hl₀, hg, B.apply_weylGroup_smul, short]
  have hl : P.root l ∈ span R {P.root i, P.root j} := by
    rw [← hl₀]
    exact add_mem (subset_span <| mem_insert_of_mem _ rfl) (subset_span <| mem_insert _ _)
  have hc : P.pairingIn ℤ k l ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne hl₁ (aux hl).1 (aux hl).2
    simp at this ⊢
    omega

  obtain ⟨g', hg'⟩ := P.bar₂ hg₂
  let m := P.weylGroupToPerm g' j
  have hm₀ : (2 : R) • P.root j + P.root i = P.root m := by rwa [weylGroup_apply_root] at hg'
  have hm₁ : B.form (P.root k) (P.root k) = B.form (P.root m) (P.root m) := by
    rw [← hm₀, hg', B.apply_weylGroup_smul, short]
  have hm : P.root m ∈ span R {P.root i, P.root j} := by
    rw [← hm₀]
    exact add_mem (Submodule.smul_mem _ _ hj) (subset_span <| mem_insert _ _)
  have hd : P.pairingIn ℤ k m ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne hm₁ (aux hm).1 (aux hm).2
    simp at this ⊢
    omega

  set a := P.pairingIn ℤ k i
  set b := P.pairingIn ℤ k j
  set c := P.pairingIn ℤ k l
  set d := P.pairingIn ℤ k m
  simp only [mem_Icc] at hb hc hd

  have habc : c = b + 3 * a := by
    suffices P.pairing k l = P.pairing k j + 3 * P.pairing k i by
      apply FaithfulSMul.algebraMap_injective ℤ R
      simp only [a, b, c, map_add, map_mul, algebraMap_pairingIn]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero k)
    calc P.pairing k l * B.form (P.root k) (P.root k)
      _ = 2 * B.form (P.root k) (P.root l) := ?_
      _ = 2 * B.form (P.root k) (P.root j) + 2 * B.form (P.root k) (P.root i) := ?_
      _ = P.pairing k j * B.form (P.root k) (P.root k) +
            P.pairing k i * B.form (P.root i) (P.root i) := ?_
      _ = (P.pairing k j + 3 * P.pairing k i) * B.form (P.root k) (P.root k) := ?_
    · rw [hl₁, ← B.two_mul_apply_root_root k l]
    · rw [← hl₀, map_add, mul_add]
    · rw [B.two_mul_apply_root_root k j, B.two_mul_apply_root_root k i, short]
    · rw [P.length_ratio hg₂ B, ← short]; ring

  have habd : d = 3 * a + 2 * b := by
    suffices P.pairing k m = 3 * P.pairing k i + 2 * P.pairing k j by
      apply FaithfulSMul.algebraMap_injective ℤ R
      simp only [a, b, d, map_add, map_mul, algebraMap_pairingIn]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero k)
    calc P.pairing k m * B.form (P.root k) (P.root k)
      _ = 2 * B.form (P.root k) (P.root m) := ?_
      _ = 2 * (2 * B.form (P.root k) (P.root j)) + 2 * B.form (P.root k) (P.root i) := ?_
      _ = 2 * P.pairing k j * B.form (P.root k) (P.root k) +
            P.pairing k i * B.form (P.root i) (P.root i) := ?_
      _ = (3 * P.pairing k i + 2 * P.pairing k j) * B.form (P.root k) (P.root k) := ?_
    · rw [hm₁, ← B.two_mul_apply_root_root k m]
    · rw [← hm₀, map_add, mul_add, map_smul, smul_eq_mul]
    · rw [B.two_mul_apply_root_root k j, B.two_mul_apply_root_root k i, short, mul_assoc]
    · rw [P.length_ratio hg₂ B, ← short]; ring

  omega

lemma foo_long (B : P.InvariantForm)
    (hk : P.root k ∉ span R {P.root i, P.root j})
    (long : B.form (P.root k) (P.root k) = B.form (P.root i) (P.root i)) :
    P.IsOrthogonal k i ∧ P.IsOrthogonal k j := by
  suffices P.pairingIn ℤ k i = 0 ∧ P.pairingIn ℤ k j = 0 by
    simp only [← B.coxeterWeight_zero_iff_isOrthogonal, ← P.algebraMap_coxeterWeightIn ℤ]
    simp [coxeterWeightIn, this.1, this.2]

  have aux {l : ι} (hl : P.root l ∈ span R {P.root i, P.root j}) :
      k ≠ l ∧ P.root k ≠ - P.root l := by
    contrapose! hk
    rcases eq_or_ne k l with rfl | hkl; · assumption
    rw [hk hkl]
    exact neg_mem hl

  have hi : P.root i ∈ span R {P.root i, P.root j} := subset_span <| mem_insert _ _
  have ha : P.pairingIn ℤ k i ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne long (aux hi).1 (aux hi).2
    simp at this ⊢
    omega

  have hb : P.pairingIn ℤ k j ∈ Icc (-3) 3 ∧ 3 ∣ P.pairingIn ℤ k j := by
    suffices P.pairingIn ℤ k j = P.pairingIn ℤ j k * 3 by
      constructor
      · have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced k j
        aesop
      · rw [this]
        exact Int.dvd_mul_left _ 3
    suffices P.pairing k j = P.pairing j k * 3 by
      apply FaithfulSMul.algebraMap_injective ℤ R
      simp only [algebraMap_pairingIn, map_mul]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero j)
    rw [mul_assoc, ← P.length_ratio hg₂ B, B.pairing_mul_eq_pairing_mul_swap j k, long]

  obtain ⟨g, hg⟩ := P.bar₃ hg₂
  let l := P.weylGroupToPerm g i
  have hl₀ : (3 : R) • P.root j + P.root i = P.root l := by rwa [weylGroup_apply_root] at hg
  have hl₁ : B.form (P.root k) (P.root k) = B.form (P.root l) (P.root l) := by
    rw [← hl₀, hg, B.apply_weylGroup_smul, long]
  have hl : P.root l ∈ span R {P.root i, P.root j} := by
    rw [← hl₀]
    exact add_mem (Submodule.smul_mem _ _ <| subset_span <| mem_insert_of_mem _ rfl)
      (subset_span <| mem_insert _ _)
  have he : P.pairingIn ℤ k l ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne hl₁ (aux hl).1 (aux hl).2
    simp at this ⊢
    omega

  obtain ⟨g', hg'⟩ := P.bar₄ hg₂
  let m := P.weylGroupToPerm g' i
  have hm₀ : (3 : R) • P.root j + (2 : R) • P.root i = P.root m := by
    rwa [weylGroup_apply_root] at hg'
  have hm₁ : B.form (P.root k) (P.root k) = B.form (P.root m) (P.root m) := by
    rw [← hm₀, hg', B.apply_weylGroup_smul, long]
  have hm : P.root m ∈ span R {P.root i, P.root j} := by
    rw [← hm₀]
    exact add_mem (Submodule.smul_mem _ _ <| subset_span <| mem_insert_of_mem _ rfl)
      (Submodule.smul_mem _ _ <| subset_span <| mem_insert _ _)
  have hf : P.pairingIn ℤ k m ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne hm₁ (aux hm).1 (aux hm).2
    simp at this ⊢
    omega

  set a := P.pairingIn ℤ k i
  set b := P.pairingIn ℤ k j
  set e := P.pairingIn ℤ k l
  set f := P.pairingIn ℤ k m
  simp only [mem_Icc] at ha hb he hf

  have habe : e = a + b := by
    suffices P.pairing k l = P.pairing k i + P.pairing k j by
      apply FaithfulSMul.algebraMap_injective ℤ R
      simp only [a, b, e, map_add, map_mul, algebraMap_pairingIn]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero k)
    calc P.pairing k l * B.form (P.root k) (P.root k)
      _ = 2 * B.form (P.root k) (P.root l) := ?_
      _ = 3 * (2 * B.form (P.root k) (P.root j)) + 2 * B.form (P.root k) (P.root i) := ?_
      _ = P.pairing k j * B.form (P.root k) (P.root k) +
            P.pairing k i * B.form (P.root i) (P.root i) := ?_
      _ = (P.pairing k i + P.pairing k j) * B.form (P.root k) (P.root k) := ?_
    · rw [hl₁, ← B.two_mul_apply_root_root k l]
    · rw [← hl₀, map_add, map_smul, smul_eq_mul]; ring
    · rw [B.two_mul_apply_root_root k j, B.two_mul_apply_root_root k i, long, P.length_ratio hg₂ B]
      ring
    · rw [long]; ring

  have habf : f = b + 2 * a := by
    suffices P.pairing k m = P.pairing k j + 2 * P.pairing k i by
      apply FaithfulSMul.algebraMap_injective ℤ R
      simp only [a, b, f, map_add, map_mul, algebraMap_pairingIn]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero k)
    calc P.pairing k m * B.form (P.root k) (P.root k)
      _ = 2 * B.form (P.root k) (P.root m) := ?_
      _ = 3 * (2 * B.form (P.root k) (P.root j)) + 2 * (2 * B.form (P.root k) (P.root i)) := ?_
      _ = P.pairing k j * B.form (P.root k) (P.root k) +
            2 * P.pairing k i * B.form (P.root i) (P.root i) := ?_
      _ = (P.pairing k j + 2 * P.pairing k i) * B.form (P.root k) (P.root k) := ?_
    · rw [hm₁, ← B.two_mul_apply_root_root k m]
    · simp only [← hm₀, map_add, map_smul, smul_eq_mul]; ring
    · rw [B.two_mul_apply_root_root k j, B.two_mul_apply_root_root k i, long, P.length_ratio hg₂ B]
      ring
    · rw [long]; ring

  omega

variable [P.IsIrreducible]

lemma foo (hk : P.root k ∉ span R {P.root i, P.root j}) :
    P.IsOrthogonal k i ∧ P.IsOrthogonal k j := by
  have : Fintype ι := Fintype.ofFinite ι
  have B : P.InvariantForm := (P.posRootForm ℤ).toInvariantForm
  have len : B.form (P.root i) (P.root i) = 3 * B.form (P.root j) (P.root j) := by
    simpa [hg₂, P.pairing_swap_eq hg₂] using B.pairing_mul_eq_pairing_mul_swap i j
  have len' : B.form (P.root i) (P.root i) ≠ B.form (P.root j) (P.root j) := by simp [len]
  rcases B.apply_eq_or_of_apply_ne len' k with long | short
  · exact foo_long P hg₂ B hk long
  · exact foo_short P hg₂ B hk short

lemma span_pair_eq_of_coxeterWeight_eq_three [Invertible (2 : R)] :
    span R {P.root i, P.root j} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {i, j} (by simp)
  rw [show P.root '' {i, j} = {P.root i, P.root j} from by aesop] at this
  apply this
  intro k hk ij hij
  have aux := P.foo hg₂ hk
  aesop

end RootPairing
