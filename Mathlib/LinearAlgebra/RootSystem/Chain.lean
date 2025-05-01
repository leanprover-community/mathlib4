/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.g2
import Mathlib.Order.Interval.Set.OrdConnectedLinear

/-!
# Chains of roots

Given roots `α` and `β`, the `α`-chain through `β` is the set of roots of the form `α + z • β`
for an integer `z`. This is known as a "root chain" and also a "root string". For linearly
independent roots in finite crystallographic root pairings, these chains are always unbroken, i.e.,
of the form: `β - q • α, ..., β - α, β, β + α, ..., β + p • α` for natural numbers `p`, `q`, and the
length, `p + q` is at most 3.

## Main definitions / results:
 * `RootPairing.chainTopCoeff`: the natural number `p` in the chain
   `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
 * `RootPairing.chainTopCoeff`: the natural number `q` in the chain
   `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
 * `RootPairing.root_add_zsmul_mem_range_iff`: every chain is an interval (aka unbroken).
 * `RootPairing.chainBotCoeff_add_chainTopCoeff_le`: every chain has length at most three.

-/

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

/-- Note that it is often more convenient to use `RootPairing.root_add_zsmul_mem_range_iff` than
to invoke this lemma directly. -/
lemma setOf_root_add_zsmul_eq_Icc_of_linearIndependent
    (h : LinearIndependent R ![P.root i, P.root j]) :
    ∃ᵉ (q ≤ 0) (p ≥ 0), {z : ℤ | P.root j + z • P.root i ∈ range P.root} = Icc q p := by
  replace h := LinearIndependent.pair_iff.mp <| h.restrict_scalars' ℤ
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  have hS₀ : 0 ∈ S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S ↦ z.property.choose) from Finite.of_injective _ this
    intro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have : z • P.root i = z' • P.root i := by
      rwa [← add_right_inj (P.root j), ← hz.choose_spec, ← hz'.choose_spec, P.root.injective.eq_iff]
    have _i : NoZeroSMulDivisors ℤ M := have := P.reflexive_left; .int_of_charZero R M
    exact Subtype.ext <| smul_left_injective ℤ (P.ne_zero i) this
  have h_ne : S.Nonempty := ⟨0, by simp [S_def]⟩
  refine ⟨sInf S, csInf_le h_fin.bddBelow hS₀, sSup S, le_csSup h_fin.bddAbove hS₀,
    (h_ne.eq_Icc_iff_int h_fin.bddBelow h_fin.bddAbove).mpr fun r ⟨k, hk⟩ s ⟨l, hl⟩ hrs ↦ ?_⟩
  by_contra! contra
  have hki_nmem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
    replace contra : r + 1 ∉ S := hrs.not_mem_of_mem_left <| by simp [contra]
    simpa only [hk, S_def, mem_setOf_eq, S] using contra
  have hki_ne : P.root k ≠ -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by omega⟩
  have hli_nmem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
    replace contra : s - 1 ∉ S := hrs.not_mem_of_mem_left <| by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_setOf_eq, S] using contra
  have hli_ne : P.root l ≠ P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by omega⟩
  have h₁ : 0 ≤ P.pairingIn ℤ k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_nmem⟩
  have h₂ : P.pairingIn ℤ k i = P.pairingIn ℤ j i + r * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hk]
    simp
  have h₃ : P.pairingIn ℤ l i ≤ 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x ↦ hli_ne (congrArg P.root x), hli_nmem⟩
  have h₄ : P.pairingIn ℤ l i = P.pairingIn ℤ j i + s * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hl]
    simp
  omega

variable (i j)

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the value `p ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainTopCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the value `q ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainBotCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

variable {i j}

lemma chainTopCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainTopCoeff i j = 0 := by
  simp only [chainTopCoeff, h, reduceDIte]

lemma chainBotCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainBotCoeff i j = 0 := by
  simp only [chainBotCoeff, h, reduceDIte]

variable (h : LinearIndependent R ![P.root i, P.root j])
include h

lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : ℕ} :
    P.root j + n • P.root i ∈ range P.root ↔ n ≤ P.chainTopCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices (n : ℤ) ∈ S ↔ n ≤ P.chainTopCoeff i j by
    simpa only [S_def, mem_setOf_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat := by
    simp [chainTopCoeff, h]
  obtain ⟨hp, h₂ : S = _⟩ :=
    (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose_spec
  rw [aux, h₂, mem_Icc]
  have := (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.1
  omega

lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : ℕ} :
    P.root j - n • P.root i ∈ range P.root ↔ n ≤ P.chainBotCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices -(n : ℤ) ∈ S ↔ n ≤ P.chainBotCoeff i j by
    simpa only [S_def, mem_setOf_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat := by
    simp [chainBotCoeff, h]
  obtain ⟨hq, p, hp, h₂ : S = _⟩ :=
    (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec
  rw [aux, h₂, mem_Icc]
  omega

lemma root_add_zsmul_mem_range_iff {z : ℤ} :
    P.root j + z • P.root i ∈ range P.root ↔
      z ∈ Icc (- P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

lemma root_sub_zsmul_mem_range_iff {z : ℤ} :
    P.root j - z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  rw [sub_eq_add_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc, mem_Icc]
  omega

omit h

private lemma chainCoeff_reflection_perm_left_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflection_perm, mem_Icc,
      reflection_apply_self, smul_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc]
    omega
  · have h' : ¬ LinearIndependent R ![P.root (-i), P.root j] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

private lemma chainCoeff_reflection_perm_right_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflection_perm, mem_Icc,
      reflection_apply_self, ← sub_neg_eq_add, ← neg_sub', neg_mem_range_root_iff,
      P.root_sub_zsmul_mem_range_iff h, mem_Icc]
  · have h' : ¬ LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

@[simp]
lemma chainTopCoeff_reflection_perm_left :
    P.chainTopCoeff (P.reflection_perm i i) j = P.chainBotCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflection_perm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)
  · simpa using this (P.chainBotCoeff i j)

@[simp]
lemma chainBotCoeff_reflection_perm_left :
    P.chainBotCoeff (P.reflection_perm i i) j = P.chainTopCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflection_perm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j)
  · simpa using this (-P.chainTopCoeff i j)

@[simp]
lemma chainTopCoeff_reflection_perm_right :
    P.chainTopCoeff i (P.reflection_perm j j) = P.chainBotCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflection_perm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j))
  · simpa using this (P.chainBotCoeff i j)

@[simp]
lemma chainBotCoeff_reflection_perm_right :
    P.chainBotCoeff i (P.reflection_perm j j) = P.chainTopCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflection_perm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j))
  · simpa using this (-P.chainTopCoeff i j)

variable (i j)

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the index of the root
`β + p • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainTopIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
      (le_refl <| P.chainTopCoeff i j) |>.choose
    else j

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the index of the root
`β - q • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainBotIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
      (le_refl <| P.chainBotCoeff i j) |>.choose
    else j

variable {i j}

@[simp]
lemma root_chainTopIdx :
    P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainTopIdx, reduceDIte, h]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
      (le_refl <| P.chainTopCoeff i j) |>.choose_spec
  · simp only [chainTopIdx, chainTopCoeff, h, reduceDIte, zero_smul, add_zero]

@[simp]
lemma root_chainBotIdx :
    P.root (P.chainBotIdx i j) = P.root j - P.chainBotCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainBotIdx, reduceDIte, h]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
      (le_refl <| P.chainBotCoeff i j) |>.choose_spec
  · simp only [chainBotIdx, chainBotCoeff, h, reduceDIte, zero_smul, sub_zero]

include h

lemma chainBotCoeff_sub_chainTopCoeff :
    P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn ℤ j i := by
  suffices ∀ i j, LinearIndependent R ![P.root i, P.root j] →
      P.chainBotCoeff i j - P.chainTopCoeff i j ≤ P.pairingIn ℤ j i by
    refine le_antisymm (this i j h) ?_
    specialize this (P.reflection_perm i i) j (by simpa)
    simp only [chainBotCoeff_reflection_perm_left, chainTopCoeff_reflection_perm_left,
      pairingIn_reflection_perm_self_right] at this
    omega
  intro i j h
  have h₁ : P.reflection i (P.root <| P.chainBotIdx i j) =
      P.root j + (P.chainBotCoeff i j - P.pairingIn ℤ j i) • P.root i := by
    simp [reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
    module
  have h₂ : P.reflection i (P.root <| P.chainBotIdx i j) ∈ range P.root := by
    rw [← root_reflection_perm]
    exact mem_range_self _
  rw [h₁, root_add_zsmul_mem_range_iff h, mem_Icc] at h₂
  omega

lemma chainTopCoeff_sub_chainBotCoeff :
    P.chainTopCoeff i j - P.chainBotCoeff i j = - P.pairingIn ℤ j i := by
  rw [← chainBotCoeff_sub_chainTopCoeff h, neg_sub]

omit h

lemma chainCoeff_chainTopIdx_aux :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j ∧
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 := by
  have aux : LinearIndependent R ![P.root i, P.root j] ↔
      LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rw [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  have h' : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by rwa [← aux]
  set S₁ : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S₁_def
  set S₂ : Set ℤ := {z | P.root (P.chainTopIdx i j) + z • P.root i ∈ range P.root} with S₂_def
  have hS₁₂ : S₂ = (fun z ↦ (-P.chainTopCoeff i j : ℤ) + z) '' S₁ := by
    ext; simp [S₁_def, S₂_def, root_chainTopIdx, add_smul, add_assoc, natCast_zsmul]
  have hS₁ : S₁ = Icc (- P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
    ext; rw [S₁_def, mem_setOf_eq, root_add_zsmul_mem_range_iff h]
  have hS₂ : S₂ = Icc (- P.chainBotCoeff i (P.chainTopIdx i j) : ℤ)
      (P.chainTopCoeff i (P.chainTopIdx i j)) := by
    ext; rw [S₂_def, mem_setOf_eq, root_add_zsmul_mem_range_iff h']
  rw [hS₁, hS₂, image_const_add_Icc, neg_add_cancel, Icc_eq_Icc_iff (by simp), neg_eq_iff_eq_neg,
    neg_add_rev, neg_neg, neg_neg] at hS₁₂
  norm_cast at hS₁₂

@[simp]
lemma chainBotCoeff_chainTopIdx :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j :=
  chainCoeff_chainTopIdx_aux.1

@[simp]
lemma chainTopCoeff_chainTopIdx :
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 :=
  chainCoeff_chainTopIdx_aux.2

include h in
lemma chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx :
    P.chainBotCoeff i j + P.chainTopCoeff i j = P.pairingIn ℤ (P.chainTopIdx i j) i := by
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : ℤ)
    _ = P.chainBotCoeff i (P.chainTopIdx i j) := by simp
    _ = P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i (P.chainTopIdx i j) := by simp
    _ = P.pairingIn ℤ (P.chainTopIdx i j) i := by rw [P.chainBotCoeff_sub_chainTopCoeff h]

lemma chainBotCoeff_add_chainTopCoeff_le_three [P.IsReduced] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 3 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i (P.chainTopIdx i j)
  aesop

lemma chainBotCoeff_add_chainTopCoeff_le_two [P.IsNotG2] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 2 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNotG2.pairingIn_mem_zero_one_two (P := P) (P.chainTopIdx i j) i
  aesop

lemma foo [P.IsNotG2] (h : P.root i + P.root j ∈ range P.root) :
    P.pairingIn ℤ i j ≤ 0 ∧ P.chainBotCoeff j i = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  have _i := P.reflexive_left
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  have aux₁ : LinearIndependent R ![P.root j, P.root i] :=
    P.linearIndependent_of_add_mem_range_root <| by rwa [add_comm]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two (i := j) (j := i)
  have aux₃ : 1 ≤ P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rcases eq_or_ne (P.chainBotCoeff j i) (P.chainTopCoeff j i) with aux₄ | aux₄ <;>
  simp only [sub_eq_zero, Nat.cast_inj, aux₄, reduceIte] <;> omega

lemma chainBotCoeff_mul_chainTopCoeff_aux_case_1 [P.IsReduced] [P.IsNotG2]
    {b : P.Base} {i j k l m : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
    (h₁ : P.root k + P.root i = P.root l)
    (h₂ : P.root k - P.root j = P.root m)
    (h₃ : P.root k + P.root i - P.root j ∈ range P.root)
    (hki' : P.pairingIn ℤ k i = 0) :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) := by
  have _i := P.reflexive_left
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  have hjk : LinearIndependent R ![P.root j, P.root k] :=
    P.linearIndependent_of_sub_mem_range_root <| by
      rw [← P.neg_mem_range_root_iff, neg_sub, h₂]; exact mem_range_self m
  replace hjk : P.root k ≠ P.root j ∧ P.root k ≠ -P.root j := by
    refine ⟨fun contra ↦ P.ne_zero m (by aesop), ?_⟩
    have := ((IsReduced.linearIndependent_iff _).mp hjk).2
    rwa [ne_eq, eq_comm, neg_eq_iff_eq_neg]
  have hki : P.pairingIn ℤ k i ≤ 0 ∧
      P.chainBotCoeff i k = if P.pairingIn ℤ k i = 0 then 1 else 0 := by
    exact P.foo <| h₁ ▸ mem_range_self l
  have hkj : 0 ≤ P.pairingIn ℤ k j ∧
      P.chainTopCoeff j k = if P.pairingIn ℤ k j = 0 then 1 else 0 := by
    have := P.foo (i := k) (j := P.reflection_perm j j)
      (by rw [root_reflection_perm, reflection_apply_self, ← sub_eq_add_neg, h₂]
          exact mem_range_self m)
    simpa using this
  have hmi : P.pairingIn ℤ m i ≤ 0 ∧
      P.chainBotCoeff i m = if P.pairingIn ℤ m i = 0 then 1 else 0 := by
    exact P.foo (i := m) (j := i) (by rwa [← h₂, add_comm_sub, ← add_sub_assoc])
  have hlj : 0 ≤ P.pairingIn ℤ l j ∧
      P.chainTopCoeff j l = if P.pairingIn ℤ l j = 0 then 1 else 0 := by
    have := P.foo (i := l) (j := P.reflection_perm j j)
      (by rwa [root_reflection_perm, reflection_apply_self, ← sub_eq_add_neg, ← h₁])
    simpa using this
  replace hki : P.chainBotCoeff i k = 1 := by simpa [hki'] using hki
  obtain ⟨n, hn⟩ := h₃
  have hnk : n ≠ k := by rintro rfl; simp [sub_eq_zero, hij, add_sub_assoc] at hn
  have hn' : P.pairingIn ℤ n k ≤ 0 := by
    by_contra! contra
    have := P.root_sub_root_mem_of_pairingIn_pos contra hnk
    rw [add_sub_assoc, ← sub_eq_iff_eq_add'] at hn
    rw [hn] at this
    exact b.sub_nmem_range_root hi hj this
  have hkj' : P.pairingIn ℤ j k = 2 := by
    suffices 2 ≤ P.pairingIn ℤ j k by
      have := IsNotG2.pairingIn_mem_zero_one_two (P := P) j k; aesop
    replace hn : P.pairingIn ℤ n k = 2 + P.pairingIn ℤ i k - P.pairingIn ℤ j k := by
      apply algebraMap_injective ℤ R
      simp only [map_add, map_sub, algebraMap_pairingIn, ← root_coroot_eq_pairing, hn]
      simp
    have hki'' : P.pairingIn ℤ i k = 0 := by rwa [pairingIn_eq_zero_iff]
    omega
  have hkj'' : P.pairingIn ℤ k j = 1 := by
    have : k ≠ j ∧ P.root k ≠ -P.root j := (IsReduced.linearIndependent_iff _).mp <|
      P.linearIndependent_of_sub_mem_range_root <| h₂ ▸ mem_range_self m
    have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k (by aesop) (by aesop)
    aesop
  replace hkj : P.chainTopCoeff j k = 0 := by
    rw [ite_cond_eq_false _ _ (by simp [hkj''])] at hkj; tauto
  have foo : P.pairing k i = 0 := by rw [← P.algebraMap_pairingIn ℤ, hki', map_zero]
  have bar : P.pairing k j = 1 := by rw [← P.algebraMap_pairingIn ℤ, hkj'', map_one]
  have aux₀ : P.pairingIn ℤ j i = - P.pairingIn ℤ m i := by
    apply algebraMap_injective ℤ R
    simp only [map_neg, algebraMap_pairingIn, ← root_coroot_eq_pairing, ← h₂]
    simp [foo]
  have aux₁ : P.pairingIn ℤ j i = 0 := by
    refine le_antisymm (b.pairingIn_le_zero_of_ne hij.symm hj hi) ?_
    rw [aux₀, neg_nonneg]
    exact hmi.1
  have aux₂ : P.pairingIn ℤ m i = 0 := by simpa [aux₁] using aux₀
  have aux₄ : P.pairingIn ℤ l j = 1 := by
    apply algebraMap_injective ℤ R
    simp only [algebraMap_pairingIn, ← root_coroot_eq_pairing, ← h₁]
    simp only [map_add, LinearMap.add_apply, root_coroot_eq_pairing, bar, algebraMap_int_eq,
      eq_intCast, Int.cast_one, add_eq_left]
    rw [pairing_eq_zero_iff, ← P.algebraMap_pairingIn ℤ, aux₁, map_zero]
  replace hmi : P.chainBotCoeff i m = 1 := by simpa [aux₂] using hmi
  replace hlj : P.chainTopCoeff j l = 0 := by simpa [aux₄] using hlj
  simp [hki, hkj, hmi, hlj]

lemma chainBotCoeff_mul_chainTopCoeff_aux_case_3a [P.IsReduced] [P.IsIrreducible] [P.IsNotG2]
    {b : P.Base} {i j k l m : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
    (h₁ : P.root k + P.root i = P.root l)
    (h₂ : P.root k - P.root j = P.root m)
    (h₃ : P.root k + P.root i - P.root j ∈ range P.root)
    (hmi : P.pairingIn ℤ m i ≤ 0 ∧ P.chainBotCoeff i m = if P.pairingIn ℤ m i = 0 then 1 else 0)
    (hlj : 0 ≤ P.pairingIn ℤ l j ∧ P.chainTopCoeff j l = if P.pairingIn ℤ l j = 0 then 1 else 0)
    (hjk : P.root k ≠ P.root j ∧ P.root k ≠ -P.root j)
    (hki' : P.pairingIn ℤ k i < 0)
    (hkj' : 0 < P.pairingIn ℤ k j) :
    ¬ (P.chainBotCoeff i m = 1 ∧ P.chainTopCoeff j l = 0) := by
  suffices ¬ (P.pairingIn ℤ m i = 0 ∧ P.pairingIn ℤ l j ≠ 0) by
    contrapose! this
    rcases ne_or_eq (P.pairingIn ℤ m i) 0 with hmi' | hmi'; · simp [hmi', this.1] at hmi
    rcases ne_or_eq (P.pairingIn ℤ l j) 0 with hlj' | hlj'; · tauto
    simp [hlj', this.2] at hlj
  rintro ⟨hmi', hlj'⟩
  have aux₀ : P.pairingIn ℤ j i = P.pairingIn ℤ k i := by
    replace hmi' : P.pairing m i = 0 := by rw [← P.algebraMap_pairingIn ℤ, hmi', map_zero]
    replace h₂ : P.root k = P.root j + P.root m := (add_eq_of_eq_sub' h₂.symm).symm
    suffices P.pairing j i = P.pairing k i from
      algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn]
    rw [← P.root_coroot_eq_pairing k, h₂]
    simpa
  have aux₁ : P.pairingIn ℤ j i < 0 := by rwa [aux₀]
  have aux₂ : 0 < - P.pairingIn ℤ i j ∧ - P.pairingIn ℤ i j < P.pairingIn ℤ k j ∧
      P.pairingIn ℤ k j ≤ 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rwa [neg_pos, P.pairingIn_lt_zero_iff]
    · suffices P.pairingIn ℤ l j = P.pairingIn ℤ i j + P.pairingIn ℤ k j by omega
      suffices P.pairing l j = P.pairing i j + P.pairing k j from
        algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add]
      rw [← P.root_coroot_eq_pairing l, ← h₁, add_comm]
      simp
    · have := IsNotG2.pairingIn_mem_zero_one_two (P := P) k j
      aesop
  replace aux₂ : P.pairingIn ℤ i j = -1 ∧ P.pairingIn ℤ k j = 2 := by omega
  have : Fintype ι := Fintype.ofFinite ι
  have B := P.posRootForm ℤ
  have aux₃ : B.rootLength i ≤ B.rootLength j ∧ B.rootLength j < B.rootLength k :=
    ⟨B.rootLength_le_of_pairingIn_eq (i := i) (j := j) <| Or.inl aux₂.1,
      B.rootLength_lt_of_pairingIn_nmem hjk.1 hjk.2 <| by aesop⟩
  have aux₄ : B.rootLength i = B.rootLength j := by
    have := (B.toInvariantForm.apply_eq_or_of_apply_ne (i := j) (j := k)
      (by simpa [RootPositiveForm.posForm, RootPositiveForm.rootLength]
            using aux₃.2.ne) i).resolve_right
      (by simpa [RootPositiveForm.posForm, RootPositiveForm.rootLength]
            using (lt_of_le_of_lt aux₃.1 aux₃.2).ne)
    simpa [RootPositiveForm.posForm, RootPositiveForm.rootLength] using this
  have aux₅ : P.pairingIn ℤ k i = -1 := by
    replace aux₄ : B.toInvariantForm.form (P.root i) (P.root i) =
        B.toInvariantForm.form (P.root j) (P.root j) := by
          simpa [RootPositiveForm.posForm, RootPositiveForm.rootLength] using aux₄
    have : P.pairingIn ℤ i j = -1 ∧ P.pairingIn ℤ j i = -1 := by
      have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne aux₄
        hij (b.root_ne_neg_of_ne hi hj hij)
      aesop
    omega
  have aux₆ : B.rootLength k ≤ B.rootLength i := B.rootLength_le_of_pairingIn_eq <| Or.inl aux₅
  omega

/-- This is Lemma 2.6 from [Geck](Geck2017).

TODO Drop the redundant assumption `[P.IsNotG2]`. -/
lemma chainBotCoeff_mul_chainTopCoeff [P.IsReduced] [P.IsIrreducible] [P.IsNotG2]
    {b : P.Base} {i j k l m : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
    (h₁ : P.root k + P.root i = P.root l)
    (h₂ : P.root k - P.root j = P.root m)
    (h₃ : P.root k + P.root i - P.root j ∈ range P.root) :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) := by
  have _i := P.reflexive_left
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  have hjk : LinearIndependent R ![P.root j, P.root k] :=
    P.linearIndependent_of_sub_mem_range_root <| by
      rw [← P.neg_mem_range_root_iff, neg_sub, h₂]; exact mem_range_self m
  replace hjk : P.root k ≠ P.root j ∧ P.root k ≠ -P.root j := by
    refine ⟨fun contra ↦ P.ne_zero m (by aesop), ?_⟩
    have := ((IsReduced.linearIndependent_iff _).mp hjk).2
    rwa [ne_eq, eq_comm, neg_eq_iff_eq_neg]
  have hik : LinearIndependent R ![P.root i, P.root k] :=
    P.linearIndependent_of_add_mem_range_root <| by
      rw [add_comm, h₁]; exact mem_range_self l
  have hik : -P.root k ≠ P.root i ∧ k ≠ i := by
    refine ⟨fun contra ↦ P.ne_zero l ?_, ?_⟩
    · rw [← contra, add_neg_cancel] at h₁
      exact h₁.symm
    · rintro rfl
      apply P.two_smul_nmem_range_root (i := k)
      rw [← two_smul R] at h₁
      rw [h₁]
      exact mem_range_self l
  have hki : P.pairingIn ℤ k i ≤ 0 ∧
      P.chainBotCoeff i k = if P.pairingIn ℤ k i = 0 then 1 else 0 := by
    exact P.foo <| h₁ ▸ mem_range_self l
  have hkj : 0 ≤ P.pairingIn ℤ k j ∧
      P.chainTopCoeff j k = if P.pairingIn ℤ k j = 0 then 1 else 0 := by
    have := P.foo (i := k) (j := P.reflection_perm j j)
      (by rw [root_reflection_perm, reflection_apply_self, ← sub_eq_add_neg, h₂]
          exact mem_range_self m)
    simpa using this
  have hmi : P.pairingIn ℤ m i ≤ 0 ∧
      P.chainBotCoeff i m = if P.pairingIn ℤ m i = 0 then 1 else 0 := by
    exact P.foo (i := m) (j := i) (by rwa [← h₂, add_comm_sub, ← add_sub_assoc])
  have hlj : 0 ≤ P.pairingIn ℤ l j ∧
      P.chainTopCoeff j l = if P.pairingIn ℤ l j = 0 then 1 else 0 := by
    have := P.foo (i := l) (j := P.reflection_perm j j)
      (by rwa [root_reflection_perm, reflection_apply_self, ← sub_eq_add_neg, ← h₁])
    simpa using this
  rcases eq_or_ne (P.pairingIn ℤ k i) 0 with hki' | hki'
  · /- Geck "Case 1" -/
    exact chainBotCoeff_mul_chainTopCoeff_aux_case_1 hi hj hij h₁ h₂ h₃ hki'
  rcases eq_or_ne (P.pairingIn ℤ k j) 0 with hkj' | hkj'
  · /- Geck "Case 2" -/
    have := P.chainBotCoeff_mul_chainTopCoeff_aux_case_1 (i := j) (j := i)
      (k := P.reflection_perm k k) (l := P.reflection_perm m m) (m := P.reflection_perm l l)
      hj hi hij.symm
      (by simp only [root_reflection_perm, reflection_apply_self]; rw [← h₂]; module)
      (by simp only [root_reflection_perm, reflection_apply_self]; rw [← h₁]; module)
      (by simp only [root_reflection_perm, reflection_apply_self]
          rw [← neg_mem_range_root_iff]; convert h₃ using 1; module)
      (by simpa)
    simpa using this.symm
  /- Geck "Case 3" -/
  replace hki' : P.pairingIn ℤ k i < 0 := by omega
  replace hkj' : 0 < P.pairingIn ℤ k j := by omega
  replace hki : P.chainBotCoeff i k = 0 := by simpa [hki'.ne] using hki.2
  replace hkj : P.chainTopCoeff j k = 0 := by simpa [hkj'.ne'] using hkj.2
  suffices P.chainBotCoeff i m = P.chainTopCoeff j l by simpa [hki, hkj]
  have aux₁ : ¬ (P.chainBotCoeff i m = 1 ∧ P.chainTopCoeff j l = 0) :=
    chainBotCoeff_mul_chainTopCoeff_aux_case_3a hi hj hij h₁ h₂ h₃ hmi hlj hjk hki' hkj'
  have aux₂ : ¬ (P.chainBotCoeff i m = 0 ∧ P.chainTopCoeff j l = 1) := by
    rw [and_comm]
    have := chainBotCoeff_mul_chainTopCoeff_aux_case_3a (i := j) (j := i)
      (k := P.reflection_perm k k) (l := P.reflection_perm m m) (m := P.reflection_perm l l)
      hj hi hij.symm
      (by simp only [root_reflection_perm, reflection_apply_self]; rw [← h₂]; module)
      (by simp only [root_reflection_perm, reflection_apply_self]; rw [← h₁]; module)
      (by simp only [root_reflection_perm, reflection_apply_self]
          rw [← neg_mem_range_root_iff]; convert h₃ using 1; module)
      (by simpa) (by simpa) (by simpa) (by simpa) (by simpa)
    simpa using this
  replace hmi : P.chainBotCoeff i m = 0 ∨ P.chainBotCoeff i m = 1 := by aesop
  replace hlj : P.chainTopCoeff j l = 0 ∨ P.chainTopCoeff j l = 1 := by aesop
  omega

end RootPairing
