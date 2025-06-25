/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.G2
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
  have hki_notMem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
    replace contra : r + 1 ∉ S := hrs.notMem_of_mem_left <| by simp [contra]
    simpa only [hk, S_def, mem_setOf_eq, S] using contra
  have hki_ne : P.root k ≠ -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by omega⟩
  have hli_notMem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
    replace contra : s - 1 ∉ S := hrs.notMem_of_mem_left <| by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_setOf_eq, S] using contra
  have hli_ne : P.root l ≠ P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by omega⟩
  have h₁ : 0 ≤ P.pairingIn ℤ k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_notMem⟩
  have h₂ : P.pairingIn ℤ k i = P.pairingIn ℤ j i + r * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hk]
    simp
  have h₃ : P.pairingIn ℤ l i ≤ 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x ↦ hli_ne (congrArg P.root x), hli_notMem⟩
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

lemma Iic_chainTopCoeff_eq :
    Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

lemma Iic_chainBotCoeff_eq :
    Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in
lemma one_le_chainTopCoeff_of_root_add_mem [P.IsReduced] (h : P.root i + P.root j ∈ range P.root) :
    1 ≤ P.chainTopCoeff i j := by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in
lemma one_le_chainBotCoeff_of_root_add_mem [P.IsReduced] (h : P.root i - P.root j ∈ range P.root) :
    1 ≤ P.chainBotCoeff i j := by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]

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

lemma setOf_root_add_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j + k • P.root i ∈ range P.root} =
      Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

lemma setOf_root_sub_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j - k • P.root i ∈ range P.root} =
      Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_setOf_eq]

lemma chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k | P.root j + k • P.root i ∈ range P.root} := by
  rw [← Iic_chainTopCoeff_eq h, csSup_Iic]

lemma chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k | P.root j - k • P.root i ∈ range P.root} := by
  rw [← Iic_chainBotCoeff_eq h, csSup_Iic]

lemma coe_chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k : ℤ | P.root j + k • P.root i ∈ range P.root} := by
  rw [setOf_root_add_zsmul_mem_eq_Icc h]
  simp

lemma coe_chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k : ℤ | P.root j - k • P.root i ∈ range P.root} := by
  rw [setOf_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h

private lemma chainCoeff_reflectionPerm_left_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, smul_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc]
    omega
  · have h' : ¬ LinearIndependent R ![P.root (-i), P.root j] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

@[deprecated (since := "2025-05-28")]
alias chainCoeff_reflection_perm_left_aux := chainCoeff_reflectionPerm_left_aux

private lemma chainCoeff_reflectionPerm_right_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, ← sub_neg_eq_add, ← neg_sub', neg_mem_range_root_iff,
      P.root_sub_zsmul_mem_range_iff h, mem_Icc]
  · have h' : ¬ LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

@[deprecated (since := "2025-05-28")]
alias chainCoeff_reflection_perm_right_aux := chainCoeff_reflectionPerm_right_aux

@[simp]
lemma chainTopCoeff_reflectionPerm_left :
    P.chainTopCoeff (P.reflectionPerm i i) j = P.chainBotCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)
  · simpa using this (P.chainBotCoeff i j)

@[deprecated (since := "2025-05-28")]
alias chainTopCoeff_reflection_perm_left := chainTopCoeff_reflectionPerm_left

@[simp]
lemma chainBotCoeff_reflectionPerm_left :
    P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j)
  · simpa using this (-P.chainTopCoeff i j)

@[deprecated (since := "2025-05-28")]
alias chainBotCoeff_reflection_perm_left := chainBotCoeff_reflectionPerm_left

@[simp]
lemma chainTopCoeff_reflectionPerm_right :
    P.chainTopCoeff i (P.reflectionPerm j j) = P.chainBotCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j))
  · simpa using this (P.chainBotCoeff i j)

@[deprecated (since := "2025-05-28")]
alias chainTopCoeff_reflection_perm_right := chainTopCoeff_reflectionPerm_right

@[simp]
lemma chainBotCoeff_reflectionPerm_right :
    P.chainBotCoeff i (P.reflectionPerm j j) = P.chainTopCoeff i j := by
  letI := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j))
  · simpa using this (-P.chainTopCoeff i j)

lemma chainBotCoeff_eq_zero_iff :
    P.chainBotCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j - P.root i ∉ range P.root := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainBotCoeff_of_not_linearIndependent h, h]
  have : P.chainBotCoeff i j = 0 ↔ Iic (P.chainBotCoeff i j) = {0} := by
    simpa [Set.ext_iff, mem_Iic, mem_singleton_iff] using ⟨fun h ↦ by simp [h], fun h ↦ by rw [← h]⟩
  simp only [h, not_true_eq_false, false_or, this, Iic_chainBotCoeff_eq h, Set.ext_iff,
    mem_setOf_eq, mem_singleton_iff]
  refine ⟨fun h' ↦ by simpa using h' 1, fun h' n ↦ ⟨fun h'' ↦ ?_, fun h'' ↦ by simp [h'']⟩⟩
  replace h' : 1 ∉ {k | P.root j - k • P.root i ∈ range P.root} := by simpa using h'
  rw [← Iic_chainBotCoeff_eq h, mem_Iic, not_le, Nat.lt_one_iff] at h'
  rw [root_sub_nsmul_mem_range_iff_le_chainBotCoeff h] at h''
  omega

lemma chainTopCoeff_eq_zero_iff :
    P.chainTopCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j + P.root i ∉ range P.root := by
  rw [← chainBotCoeff_reflectionPerm_left]
  simp [-chainBotCoeff_reflectionPerm_left, chainBotCoeff_eq_zero_iff]

include h

lemma chainBotCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + 1 := by
  have h' : LinearIndependent R ![P.root i, P.root k] := by simpa [hk, add_comm]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_one, coe_chainBotCoeff_eq_sSup h', coe_chainBotCoeff_eq_sSup h]
  have (z : ℤ) : P.root k - z • P.root i = P.root j - (z - 1) • P.root i := by rw [hk]; module
  replace this : {z : ℤ | P.root k - z • P.root i ∈ range P.root} =
      OrderIso.addRight 1 '' {n | P.root j - n • P.root i ∈ range P.root} := by
    simp [this, sub_eq_add_neg]
  have bdd : BddAbove {z : ℤ | P.root j - z • P.root i ∈ range P.root} := by
    rw [setOf_root_sub_zsmul_mem_eq_Icc h]
    exact bddAbove_Icc
  rw [this, ← OrderIso.map_csSup' _ ⟨0, by simp⟩ bdd, OrderIso.addRight_apply]

lemma chainTopCoeff_of_sub {k : ι} (hk : P.root k = P.root j - P.root i) :
    P.chainTopCoeff i k = P.chainTopCoeff i j + 1 := by
  letI := P.indexNeg
  replace hk : P.root k = P.root j + P.root (-i) := by simpa [sub_eq_add_neg] using hk
  simpa using chainBotCoeff_of_add (by simpa) hk

omit h
@[deprecated (since := "2025-05-28")]
alias chainBotCoeff_reflection_perm_right := chainBotCoeff_reflectionPerm_right

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
    specialize this (P.reflectionPerm i i) j (by simpa)
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCoeff_reflectionPerm_left,
      pairingIn_reflectionPerm_self_right] at this
    omega
  intro i j h
  have h₁ : P.reflection i (P.root <| P.chainBotIdx i j) =
      P.root j + (P.chainBotCoeff i j - P.pairingIn ℤ j i) • P.root i := by
    simp [reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
    module
  have h₂ : P.reflection i (P.root <| P.chainBotIdx i j) ∈ range P.root := by
    rw [← root_reflectionPerm]
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

variable (i j) in
lemma chainBotCoeff_add_chainTopCoeff_le_two [P.IsNotG2] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 2 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNotG2.pairingIn_mem_zero_one_two (P := P) (P.chainTopIdx i j) i
  aesop

/-- For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if the sum of two
roots is a root, they cannot make an acute angle.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base. Then the roots
`α + β` and `2α + β` make an angle `π / 3` even though `3α + 2β` is a root. We can even witness as:
```lean
example (P : RootPairing ι R M N) [P.EmbeddedG2] :
    P.pairingIn ℤ (EmbeddedG2.shortAddLong P) (EmbeddedG2.twoShortAddLong P) = 1 := by
  simp
```
-/
lemma pairingIn_le_zero_of_root_add_mem [P.IsNotG2] (h : P.root i + P.root j ∈ range P.root) :
    P.pairingIn ℤ i j ≤ 0 := by
  have aux₁ := P.linearIndependent_of_add_mem_range_root' <| add_comm (P.root i) (P.root j) ▸ h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two j i
  have aux₃ : 1 ≤ P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  omega

lemma zero_le_pairingIn_of_root_sub_mem [P.IsNotG2] (h : P.root i - P.root j ∈ range P.root) :
    0 ≤ P.pairingIn ℤ i j := by
  replace h : P.root i + P.root (P.reflectionPerm j j) ∈ range P.root := by
    simpa [-mem_range, ← sub_eq_add_neg]
  simpa using P.pairingIn_le_zero_of_root_add_mem h

/-- For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if the sum of two
roots is a root, the bottom chain coefficient is either one or zero according to whether they are
perpendicular.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base. Then the roots
`α` and `α + β` provide a counterexample. -/
lemma chainBotCoeff_if_one_zero [P.IsNotG2] (h : P.root i + P.root j ∈ range P.root) :
    P.chainBotCoeff i j = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  have _i := P.reflexive_left
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two i j
  have aux₃ : 1 ≤ P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotCoeff i j) (P.chainTopCoeff i j) with aux₄ | aux₄ <;>
  simp_rw [P.pairingIn_eq_zero_iff (i := i) (j := j), ← P.chainBotCoeff_sub_chainTopCoeff aux₁,
    sub_eq_zero, Nat.cast_inj, aux₄, reduceIte] <;>
  omega

lemma chainTopCoeff_if_one_zero [P.IsNotG2] (h : P.root i - P.root j ∈ range P.root) :
    P.chainTopCoeff i j = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  letI := P.indexNeg
  replace h : P.root i + P.root (-j) ∈ range P.root := by simpa [← sub_eq_add_neg] using h
  simpa using P.chainBotCoeff_if_one_zero h

section chainBotCoeff_mul_chainTopCoeff

/-! The proof of lemma 2.6 from [Geck](Geck2017). -/

variable {b : P.Base} {i j k l m : ι}
  (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
  (h₁ : P.root k + P.root i = P.root l)
  (h₂ : P.root k - P.root j = P.root m)
  (h₃ : P.root k + P.root i - P.root j ∈ range P.root)

-- TODO Turn this `variable` into a lemma: it is implied by the assumptions above.
variable [P.IsNotG2]

lemma chainBotCoeff_mul_chainTopCoeff.aux_0 (hik_mem : P.root k + P.root i ∈ range P.root) :
    P.pairingIn ℤ k i = 0 ∨ (P.pairingIn ℤ k i < 0 ∧ P.chainBotCoeff i k = 0) := by
  have _i := P.reflexive_left
  have := pairingIn_le_zero_of_root_add_mem hik_mem
  rw [add_comm] at hik_mem
  rw [P.chainBotCoeff_if_one_zero hik_mem, ite_eq_right_iff, P.pairingIn_eq_zero_iff (i := i)]
  omega

include hi hj hij h₁ h₂ h₃

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
  have h₃' : P.root (-k) + P.root j - P.root i ∈ range P.root := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]
    rw [← neg_mem_range_root_iff]; convert h₃ using 1; abel
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
