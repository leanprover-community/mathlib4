/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
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
lemma setOf_root_add_zsmul_eq_Icc_of_linInd
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
    then (P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose_spec.2.choose.toNat
    else 0

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the value `q ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainBotCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose).toNat
    else 0

variable {i j}

lemma chainTopCoeff_of_not_linInd (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainTopCoeff i j = 0 := by
  simp only [chainTopCoeff, h, reduceDIte]

lemma chainBotCoeff_of_not_linInd (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
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
      (P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose_spec.2.choose.toNat := by
    simp [chainTopCoeff, h]
  obtain ⟨hp, h₂ : S = _⟩ := (P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose_spec.2.choose_spec
  rw [aux, h₂, mem_Icc]
  have := (P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose_spec.1
  omega

lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : ℕ} :
    P.root j - n • P.root i ∈ range P.root ↔ n ≤ P.chainBotCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices -(n : ℤ) ∈ S ↔ n ≤ P.chainBotCoeff i j by
    simpa only [S_def, mem_setOf_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose).toNat := by
    simp [chainBotCoeff, h]
  obtain ⟨hq, p, hp, h₂ : S = _⟩ := (P.setOf_root_add_zsmul_eq_Icc_of_linInd h).choose_spec
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

private lemma chainCoeff_relfection_perm_aux :
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
    simp only [chainTopCoeff_of_not_linInd h, chainTopCoeff_of_not_linInd h',
      chainBotCoeff_of_not_linInd h, chainBotCoeff_of_not_linInd h']

@[simp]
lemma chainTopCoeff_relfection_perm :
    P.chainTopCoeff (P.reflection_perm i i) j = P.chainBotCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_relfection_perm_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)
  · simpa using this (P.chainBotCoeff i j)

@[simp]
lemma chainBotCoeff_relfection_perm :
    P.chainBotCoeff (P.reflection_perm i i) j = P.chainTopCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_relfection_perm_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j)
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
    simp only [chainBotCoeff_relfection_perm, chainTopCoeff_relfection_perm,
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
  swap; · simp [chainTopCoeff_of_not_linInd, chainBotCoeff_of_not_linInd, h]
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

lemma chainBotCoeff_add_chainTopCoeff_le [P.IsReduced] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 3 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linInd, chainBotCoeff_of_not_linInd, h]
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  rw [← Int.ofNat_le]
  calc (↑(P.chainBotCoeff i j + P.chainTopCoeff i j) : ℤ)
    _ = P.chainBotCoeff i (P.chainTopIdx i j) := by simp
    _ = P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i (P.chainTopIdx i j) := by simp
    _ = P.pairingIn ℤ (P.chainTopIdx i j) i := by rw [P.chainBotCoeff_sub_chainTopCoeff h]
    _ ≤ 3 := ?_
  have _i := P.reflexive_left
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i (P.chainTopIdx i j)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
  omega

end RootPairing
