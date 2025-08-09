/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Supporting lemmas for Geck's construction of a Lie algebra associated to a root system
-/

open Set
open FaithfulSMul (algebraMap_injective)

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

local notation "Φ" => range P.root
local notation "α" => P.root

namespace Base

variable {b : P.Base} (i j k : ι) (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support)
include hij hi hj

/-- This is Lemma 2.5 (a) from [Geck](Geck2017). -/
lemma root_sub_root_mem_of_mem_of_mem (hk : α k + α i - α j ∈ Φ)
    (hkj : k ≠ j) (hk' : α k + α i ∈ Φ) :
    α k - α j ∈ Φ := by
  rcases lt_or_ge 0 (P.pairingIn ℤ j k) with hm | hm
  · rw [← neg_mem_range_root_iff, neg_sub]
    exact P.root_sub_root_mem_of_pairingIn_pos hm hkj.symm
  obtain ⟨l, hl⟩ := hk
  have hli : l ≠ i := by
    rintro rfl
    rw [add_comm, add_sub_assoc, left_eq_add, sub_eq_zero, P.root.injective.eq_iff] at hl
    exact hkj hl
  suffices 0 < P.pairingIn ℤ l i by
    convert P.root_sub_root_mem_of_pairingIn_pos this hli using 1
    rw [hl]
    module
  have hkl : l ≠ k := by rintro rfl; exact hij <| by simpa [add_sub_assoc, sub_eq_zero] using hl
  replace hkl : P.pairingIn ℤ l k ≤ 0 := by
    suffices α l - α k ∉ Φ by contrapose! this; exact P.root_sub_root_mem_of_pairingIn_pos this hkl
    replace hl : α l - α k = α i - α j := by rw [hl]; module
    rw [hl]
    exact b.sub_notMem_range_root hi hj
  have hki : P.pairingIn ℤ i k ≤ -2 := by
    suffices P.pairingIn ℤ l k = 2 + P.pairingIn ℤ i k - P.pairingIn ℤ j k by linarith
    apply algebraMap_injective ℤ R
    simp only [algebraMap_pairingIn, map_sub, map_add, map_ofNat]
    simpa using (P.coroot' k : M →ₗ[R] R).congr_arg hl
  replace hki : P.pairingIn ℤ k i = -1 := by
    replace hk' : α i ≠ - α k := by
      rw [← sub_ne_zero, sub_neg_eq_add, add_comm]
      intro contra
      rw [contra] at hk'
      exact P.ne_zero _ hk'.choose_spec
    have aux (h : P.pairingIn ℤ i k = -2) : ¬P.pairingIn ℤ k i = -2 := by
      have := P.reflexive_left
      contrapose! hk'; exact (P.pairingIn_neg_two_neg_two_iff ℤ i k).mp ⟨h, hk'⟩
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i k
    aesop -- #24551 (this should be faster)
  replace hki : P.pairing k i = -1 := by rw [← P.algebraMap_pairingIn ℤ, hki]; simp
  have : P.pairingIn ℤ l i = 1 - P.pairingIn ℤ j i := by
    apply algebraMap_injective ℤ R
    simp only [algebraMap_pairingIn, map_sub, map_one, algebraMap_pairingIn]
    convert (P.coroot' i : M →ₗ[R] R).congr_arg hl using 1
    simp only [PerfectPairing.flip_apply_apply, map_sub, map_add,
      root_coroot_eq_pairing, hki, pairing_same]
    ring
  replace hij := pairingIn_le_zero_of_ne b hij.symm hj hi
  omega

/-- This is Lemma 2.5 (b) from [Geck](Geck2017). -/
lemma root_add_root_mem_of_mem_of_mem (hk : α k + α i - α j ∈ Φ)
    (hkj : α k ≠ -α i) (hk' : α k - α j ∈ Φ) :
    α k + α i ∈ Φ := by
  let _i := P.indexNeg
  replace hk : α (-k) + α j - α i ∈ Φ := by
    rw [← neg_mem_range_root_iff]
    convert hk using 1
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
    module
  rw [← neg_mem_range_root_iff]
  convert b.root_sub_root_mem_of_mem_of_mem j i (-k) hij.symm hj hi hk (by contrapose! hkj; aesop)
    (by convert P.neg_mem_range_root_iff.mpr hk' using 1; simp [neg_add_eq_sub]) using 1
  simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
  module

lemma root_sub_mem_iff_root_add_mem (hkj : k ≠ j) (hkj' : α k ≠ -α i) (hk : α k + α i - α j ∈ Φ) :
    α k - α j ∈ Φ ↔ α k + α i ∈ Φ :=
  ⟨b.root_add_root_mem_of_mem_of_mem i j k hij hi hj hk hkj',
   b.root_sub_root_mem_of_mem_of_mem i j k hij hi hj hk hkj⟩

end Base

section chainBotCoeff_mul_chainTopCoeff

/-! The proof of Lemma 2.6 from [Geck](Geck2017). -/

variable {b : P.Base} {i j k l m : ι}

private lemma chainBotCoeff_mul_chainTopCoeff.aux_0 [P.IsNotG2]
    (hik_mem : P.root k + P.root i ∈ range P.root) :
    P.pairingIn ℤ k i = 0 ∨ (P.pairingIn ℤ k i < 0 ∧ P.chainBotCoeff i k = 0) := by
  have _i := P.reflexive_left
  have := pairingIn_le_zero_of_root_add_mem hik_mem
  rw [add_comm] at hik_mem
  rw [P.chainBotCoeff_if_one_zero hik_mem, ite_eq_right_iff, P.pairingIn_eq_zero_iff (i := i)]
  omega

variable [P.IsReduced] [P.IsIrreducible]
  (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
  (h₁ : P.root k + P.root i = P.root l)
  (h₂ : P.root k - P.root j = P.root m)
  (h₃ : P.root k + P.root i - P.root j ∈ range P.root)

include hi hj hij h₁ h₂ h₃

lemma chainBotCoeff_mul_chainTopCoeff.isNotG2 : P.IsNotG2 := by
  have _i : NoZeroSMulDivisors ℤ M := have _i := P.reflexive_left; .int_of_charZero R M
  rw [← P.not_isG2_iff_isNotG2]
  intro contra
  obtain ⟨n, h₃⟩ := h₃
  obtain ⟨x, y, h₀⟩ : ∃ x y : ℤ, x • P.root i + y • P.root j = P.root k := by
    rw [← Submodule.mem_span_pair, IsG2.span_eq_rootSpan_int hi hj hij]
    exact Submodule.subset_span (mem_range_self k)
  let s : Set ℤ := {-3, -1, 0, 1, 3}
  let A : ℤ := P.pairingIn ℤ j i
  have hki  : P.root k ≠  P.root i := fun contra ↦ by
    replace h₁ : 2 • P.root i = P.root l := by rwa [contra, ← two_nsmul] at h₁
    exact P.nsmul_notMem_range_root ⟨_, h₁.symm⟩
  have hki' : P.root k ≠ -P.root i := fun contra ↦ by
    replace h₁ : P.root l = 0 := by rwa [contra, neg_add_cancel, eq_comm] at h₁
    exact P.ne_zero _ h₁
  have hli  : P.root l ≠  P.root i := fun contra ↦ by
    replace h₁ : P.root k = 0 := by rwa [contra, add_eq_right] at h₁
    exact P.ne_zero _ h₁
  have hli' : P.root l ≠ -P.root i := fun contra ↦ by
    replace h₁ : P.root k = 2 • P.root l := by
      rwa [← neg_eq_iff_eq_neg.mpr contra, ← sub_eq_add_neg, sub_eq_iff_eq_add, ← two_nsmul] at h₁
    exact P.nsmul_notMem_range_root ⟨_, h₁⟩
  have hmi  : P.root m ≠  P.root i := fun contra ↦ by
    replace h₂ : P.root k = P.root i + P.root j := by rwa [contra, sub_eq_iff_eq_add] at h₂
    replace h₃ : P.root n = 2 • P.root i := by rw [h₃, h₂]; abel
    exact P.nsmul_notMem_range_root ⟨_, h₃⟩
  have hmi' : P.root m ≠ -P.root i := fun contra ↦ by
    replace h₂ : P.root k = -P.root i + P.root j := by rwa [contra, sub_eq_iff_eq_add] at h₂
    replace h₃ : P.root n = 0 := by rw [h₃, h₂]; abel
    exact P.ne_zero _ h₃
  have hni  : P.root n ≠  P.root i := fun contra ↦ by
    replace h₃ : P.root k = P.root j := by
      rwa [contra, add_comm, add_sub_assoc, left_eq_add, sub_eq_zero] at h₃
    replace h₂ : P.root m = 0 := by rw [← h₂, h₃, sub_self]
    exact P.ne_zero _ h₂
  have hni' : P.root n ≠ -P.root i := fun contra ↦ by
    replace h₃ : 2 • P.root n = P.root m := by
      rwa [← neg_eq_iff_eq_neg.mpr contra, add_comm, add_sub_assoc, eq_neg_add_iff_add_eq,
        ← two_nsmul, h₂] at h₃
    exact P.nsmul_notMem_range_root ⟨_, h₃.symm⟩
  replace h₁ : 2 * (x + 1) + A * y ∈ s := by
    convert IsG2.pairingIn_mem_zero_one_three P l i hli hli'
    replace h₁ : P.root l = (x + 1) • P.root i + y • P.root j := by rw [← h₁, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := i) h₁, pairingIn_same,
      Int.zsmul_eq_mul, Int.zsmul_eq_mul]
    ring
  replace h₂ : 2 * x + A * (y - 1) ∈ s := by
    convert IsG2.pairingIn_mem_zero_one_three P m i hmi hmi'
    replace h₂ : P.root m = x • P.root i + (y - 1) • P.root j := by rw [← h₂, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := i) h₂, pairingIn_same,
      Int.zsmul_eq_mul, Int.zsmul_eq_mul]
    ring
  replace h₃ : 2 * (x + 1) + A * (y - 1) ∈ s := by
    convert IsG2.pairingIn_mem_zero_one_three P n i hni hni'
    replace h₃ : P.root n = (x + 1) • P.root i + (y - 1) • P.root j := by rw [h₃, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := i) h₃, pairingIn_same,
      Int.zsmul_eq_mul, Int.zsmul_eq_mul]
    ring
  replace h₀ : 2 * x + A * y ∈ s := by
    convert IsG2.pairingIn_mem_zero_one_three P k i hki hki'
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (j := i) h₀.symm, pairingIn_same,
      Int.zsmul_eq_mul, Int.zsmul_eq_mul]
    ring
  have hA : A ∈ s := IsG2.pairingIn_mem_zero_one_three P j i (P.root.injective.ne_iff.mpr hij.symm)
    (b.root_ne_neg_of_ne hj hi hij.symm)
  subst s
  simp only [mem_insert_iff, mem_singleton_iff] at h₀ h₁ h₂ h₃ hA
  rcases hA with hA | hA | hA | hA | hA <;> rw [hA] at h₀ h₁ h₂ h₃ <;> omega

/- An auxiliary result en route to `RootPairing.chainBotCoeff_mul_chainTopCoeff`. -/
private lemma chainBotCoeff_mul_chainTopCoeff.aux_1
    (hki : P.pairingIn ℤ k i = 0) :
    have _i := P.reflexive_left; letI := P.indexNeg
    P.root i + P.root m ∈ range P.root → P.root j + P.root (-l) ∈ range P.root →
      P.root j + P.root (-k) ∈ range P.root →
      (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
        (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) := by
  intro _ him_mem hjl_mem hjk_mem
  /- Setup some typeclasses and name the 6th root `n`. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  letI := P.indexNeg
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  obtain ⟨n, hn⟩ := h₃
  /- Establish basic relationships about roots and their sums / differences. -/
  have hnk_ne : n ≠ k := by rintro rfl; simp [sub_eq_zero, hij, add_sub_assoc] at hn
  have hkj_ne : k ≠ j ∧ P.root k ≠ -P.root j := (IsReduced.linearIndependent_iff _).mp <|
    P.linearIndependent_of_sub_mem_range_root <| h₂ ▸ mem_range_self m
  have hnk_notMem : P.root n - P.root k ∉ range P.root := by
    convert b.sub_notMem_range_root hi hj using 2; rw [hn]; module
  /- Calculate some auxiliary relationships between root pairings. -/
  have aux₀ : P.pairingIn ℤ j i = - P.pairingIn ℤ m i := by
    suffices P.pairing j i = - P.pairing m i from
      algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_neg]
    replace hki : P.pairing k i = 0 := by rw [← P.algebraMap_pairingIn ℤ, hki, map_zero]
    simp only [← root_coroot_eq_pairing, ← h₂]
    simp [hki]
  have aux₁ : P.pairingIn ℤ j i = 0 := by
    refine le_antisymm (b.pairingIn_le_zero_of_ne hij.symm hj hi) ?_
    rw [aux₀, neg_nonneg]
    refine P.pairingIn_le_zero_of_root_add_mem ⟨n, ?_⟩
    rw [hn, ← h₂]
    abel
  /- Calculate the pairings between four key root pairs. -/
  have key₁ : P.pairingIn ℤ i k = 0 := by rwa [pairingIn_eq_zero_iff]
  have key₂ : P.pairingIn ℤ i m = 0 := P.pairingIn_eq_zero_iff.mp <| by simpa [aux₁] using aux₀
  have key₃ : P.pairingIn ℤ j k = 2 := by
    suffices 2 ≤ P.pairingIn ℤ j k by have := IsNotG2.pairingIn_mem_zero_one_two (P := P) j k; aesop
    have hn₁ : P.pairingIn ℤ n k = 2 + P.pairingIn ℤ i k - P.pairingIn ℤ j k := by
      apply algebraMap_injective ℤ R
      simp only [map_add, map_sub, algebraMap_pairingIn, ← root_coroot_eq_pairing, hn]
      simp
    have hn₂ : P.pairingIn ℤ n k ≤ 0 := by
      by_contra! contra; exact hnk_notMem <| P.root_sub_root_mem_of_pairingIn_pos contra hnk_ne
    omega
  have key₄ : P.pairingIn ℤ l j = 1 := by
    have hij : P.pairing i j = 0 := by
      rw [pairing_eq_zero_iff, ← P.algebraMap_pairingIn ℤ, aux₁, map_zero]
    have hkj : P.pairing k j = 1 := by
      rw [← P.algebraMap_pairingIn ℤ]
      have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k (by aesop) (by aesop)
      aesop
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, ← root_coroot_eq_pairing, ← h₁]
    simp [hkj, hij]
  replace key₄ : P.pairingIn ℤ j l ≠ 0 := by rw [ne_eq, P.pairingIn_eq_zero_iff]; omega
  /- Calculate the value of each of the four terms in the goal. -/
  have hik_mem : P.root i + P.root k ∈ range P.root := ⟨l, by rw [← h₁, add_comm]⟩
  simp only [P.chainBotCoeff_if_one_zero, hik_mem, him_mem, hjl_mem, hjk_mem]
  simp [key₁, key₂, key₃, key₄]

/- An auxiliary result en route to `RootPairing.chainBotCoeff_mul_chainTopCoeff`. -/
open RootPositiveForm in
private lemma chainBotCoeff_mul_chainTopCoeff.aux_2
    (hki' : P.pairingIn ℤ k i < 0) (hkj' : 0 < P.pairingIn ℤ k j) :
    have _i := P.reflexive_left; letI := P.indexNeg
    P.root i + P.root m ∈ range P.root → P.root j + P.root (-l) ∈ range P.root →
      P.root j + P.root (-k) ∈ range P.root →
      ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) := by
  intro _ him_mem hjl_mem hjk_mem
  letI := P.indexNeg
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  /- Establish basic relationships about roots and their sums / differences. -/
  have hkj_ne : k ≠ j ∧ P.root k ≠ -P.root j := (IsReduced.linearIndependent_iff _).mp <|
    P.linearIndependent_of_sub_mem_range_root <| h₂ ▸ mem_range_self m
  have hlj_mem : P.root l - P.root j ∈ range P.root := by rwa [← h₁]
  /- It is sufficient to prove that two key pairings vanish. -/
  suffices ¬ (P.pairingIn ℤ m i = 0 ∧ P.pairingIn ℤ l j ≠ 0) by
    contrapose! this
    rcases ne_or_eq (P.pairingIn ℤ m i) 0 with hmi | hmi
    · simpa [hmi, this.1, P.pairingIn_eq_zero_iff (i := i)] using chainBotCoeff_if_one_zero him_mem
    refine ⟨hmi, fun hlj ↦ ?_⟩
    rw [chainBotCoeff_if_one_zero hjl_mem] at this
    simp [P.pairingIn_eq_zero_iff (i := j), hlj] at this
  /- Assume for contradiction that the two pairings do not vanish. -/
  rintro ⟨hmi, hlj⟩
  /- Use the assumptions to calculate various relationships between root pairings. -/
  have aux₀ : P.pairingIn ℤ j i = P.pairingIn ℤ k i := by
    suffices P.pairing j i = P.pairing k i from
      algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn]
    replace h₂ : P.root k = P.root j + P.root m := (add_eq_of_eq_sub' h₂.symm).symm
    simpa [← P.root_coroot_eq_pairing k, h₂, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨aux₁, aux₂⟩ : P.pairingIn ℤ i j = -1 ∧ P.pairingIn ℤ k j = 2 := by
    suffices 0 < - P.pairingIn ℤ i j ∧ - P.pairingIn ℤ i j < P.pairingIn ℤ k j ∧
      P.pairingIn ℤ k j ≤ 2 by omega
    refine ⟨?_, ?_, ?_⟩
    · rwa [neg_pos, P.pairingIn_lt_zero_iff, aux₀]
    · suffices P.pairingIn ℤ l j = P.pairingIn ℤ i j + P.pairingIn ℤ k j by
        have := zero_le_pairingIn_of_root_sub_mem hlj_mem; omega
      suffices P.pairing l j = P.pairing i j + P.pairing k j from
        algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add]
      simp [← P.root_coroot_eq_pairing l, ← h₁, add_comm]
    · have := IsNotG2.pairingIn_mem_zero_one_two (P := P) k j
      aesop
  /- Choose a positive invariant form. -/
  obtain B : RootPositiveForm ℤ P := have : Fintype ι := Fintype.ofFinite ι; P.posRootForm ℤ
  /- Calculate root length relationships implied by the pairings calculated above. -/
  have ⟨aux₃, aux₄⟩ : B.rootLength i = B.rootLength j ∧ B.rootLength j < B.rootLength k := by
    have hij_le : B.rootLength i ≤ B.rootLength j := B.rootLength_le_of_pairingIn_eq <| Or.inl aux₁
    have hjk_lt : B.rootLength j < B.rootLength k :=
      B.rootLength_lt_of_pairingIn_notMem (by aesop) hkj_ne.2 <| by aesop
    refine ⟨?_, hjk_lt⟩
    simpa [posForm, rootLength] using (B.toInvariantForm.apply_eq_or_of_apply_ne (i := j) (j := k)
      (by simpa [posForm, rootLength] using hjk_lt.ne) i).resolve_right
      (by simpa [posForm, rootLength] using (lt_of_le_of_lt hij_le hjk_lt).ne)
  /- Use the root length results to calculate a final root pairing. -/
  have aux₅ : P.pairingIn ℤ k i = -1 := by
    suffices P.pairingIn ℤ j i = -1 by omega
    have aux : B.toInvariantForm.form (P.root i) (P.root i) =
        B.toInvariantForm.form (P.root j) (P.root j) := by simpa [posForm, rootLength] using aux₃
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne aux hij (b.root_ne_neg_of_ne hi hj hij)
    aesop
  /- Use the newly calculated pairing result to obtain further information about root lengths. -/
  have aux₆ : B.rootLength k ≤ B.rootLength i := B.rootLength_le_of_pairingIn_eq <| Or.inl aux₅
  /- We now have contradictory information about root lengths. -/
  omega

open chainBotCoeff_mul_chainTopCoeff in
/-- This is Lemma 2.6 from [Geck](Geck2017). -/
lemma chainBotCoeff_mul_chainTopCoeff :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) := by
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  have _i := P.reflexive_left
  letI := P.indexNeg
  suffices (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
      (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) by simpa
  /- Establish basic relationships about roots and their sums / differences. -/
  have him_mem : P.root i + P.root m ∈ range P.root := by rw [← h₂]; convert h₃ using 1; abel
  have hik_mem : P.root k + P.root i ∈ range P.root := h₁ ▸ mem_range_self l
  have hjk_mem : P.root j + P.root (-k) ∈ range P.root := by
    convert mem_range_self (-m) using 1; simpa [sub_eq_add_neg] using congr(-$h₂)
  have hjl_mem : P.root j + P.root (-l) ∈ range P.root := by
    rw [h₁, ← neg_mem_range_root_iff] at h₃; convert h₃ using 1; simp [sub_eq_add_neg]
  have h₁' : P.root (-k) - P.root i = P.root (-l) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₁]; abel
  have h₂' : P.root (-k) + P.root j = P.root (-m) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₂]; abel
  have h₃' : P.root (-k) + P.root j - P.root i ∈ range P.root := by grind
  /- Proceed to the main argument, following Geck's case splits. It's all just bookkeeping. -/
  rcases aux_0 hik_mem with hki | ⟨hki, hik⟩
  · /- Geck "Case 1" -/
    exact aux_1 hi hj hij h₁ h₂ h₃ hki him_mem hjl_mem hjk_mem
  rw [add_comm] at hik_mem hjk_mem
  rcases aux_0 hjk_mem with hkj | ⟨hkj, hjk⟩
  · /- Geck "Case 2" -/
    simpa only [neg_neg] using (aux_1 hj hi hij.symm h₂' h₁' h₃' hkj hjl_mem
      (by simpa only [neg_neg]) (by simpa only [neg_neg])).symm
  /- Geck "Case 3" -/
  suffices P.chainBotCoeff i m = P.chainBotCoeff j (-l) by rw [hik, hjk, this]
  have aux₁ : ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) :=
    aux_2 hi hj hij h₁ h₂ h₃ hki (by simpa using hkj) him_mem hjl_mem <| by rwa [add_comm]
  have aux₂ : ¬(P.chainBotCoeff j (-l) = 1 ∧ P.chainBotCoeff i m = 0) := by
    simpa using aux_2 hj hi hij.symm h₂' h₁' h₃' hkj (by simpa)
      hjl_mem (by simpa only [neg_neg]) (by simpa only [neg_neg])
  have aux₃ : P.chainBotCoeff i m = 0 ∨ P.chainBotCoeff i m = 1 := by
    have := P.chainBotCoeff_if_one_zero him_mem
    split at this <;> simp [this]
  have aux₄ : P.chainBotCoeff j (-l) = 0 ∨ P.chainBotCoeff j (-l) = 1 := by
    have := P.chainBotCoeff_if_one_zero hjl_mem
    split at this <;> simp only [this, true_or, or_true]
  omega

end chainBotCoeff_mul_chainTopCoeff

end RootPairing
