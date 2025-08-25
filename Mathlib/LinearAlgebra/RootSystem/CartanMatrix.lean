/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
* `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
  respect to a base `b`.
* `RootPairing.Base.cartanMatrix_nondegenerate`: the Cartan matrix is non-degenerate.
* `RootPairing.Base.induction_on_cartanMatrix`: an induction principle expressing the connectedness
  of the Dynkin diagram of an irreducible root pairing.

-/

noncomputable section

open FaithfulSMul (algebraMap_injective)
open Function Set
open Module.End (invtSubmodule mem_invtSubmodule)
open Submodule (span subset_span)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing.Base

variable (S : Type*) [CommRing S] [Algebra S R]
  {P : RootPairing ι R M N} [P.IsValuedIn S] (b : P.Base)

/-- The Cartan matrix of a root pairing, taking values in `S`, with respect to a base `b`.

See also `RootPairing.Base.cartanMatrix`. -/
def cartanMatrixIn :
    Matrix b.support b.support S :=
  .of fun i j ↦ P.pairingIn S i j

lemma cartanMatrixIn_def (i j : b.support) :
    b.cartanMatrixIn S i j = P.pairingIn S i j :=
  rfl

@[simp]
lemma algebraMap_cartanMatrixIn_apply (i j : b.support) :
    algebraMap S R (b.cartanMatrixIn S i j) = P.pairing i j := by
  simp [cartanMatrixIn_def]

@[simp]
lemma cartanMatrixIn_apply_same [FaithfulSMul S R] (i : b.support) :
    b.cartanMatrixIn S i i = 2 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [cartanMatrixIn_def, map_ofNat]

/- If we generalised the notion of `RootPairing.Base` to work relative to an assumption
`[P.IsValuedIn S]` then such a base would provide basis of `P.rootSpan S` and we could avoid
using `Matrix.map` below. -/
lemma cartanMatrixIn_mul_diagonal_eq {P : RootSystem ι R M N} [P.IsValuedIn S]
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] :
    (b.cartanMatrixIn S).map (algebraMap S R) *
      (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)) =
      (2 : R) • BilinForm.toMatrix b.toWeightBasis B.form := by
  ext
  simp [B.two_mul_apply_root_root]

lemma cartanMatrixIn_nondegenerate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S]
    {P : RootSystem ι R M N} [P.IsValuedIn S] [Fintype ι] [P.IsAnisotropic] (b : P.Base) :
    (b.cartanMatrixIn S).Nondegenerate := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • BilinForm.toMatrix b.toWeightBasis B.form).Nondegenerate := by
    rwa [Matrix.Nondegenerate.smul_iff two_ne_zero, LinearMap.BilinForm.nondegenerate_toMatrix_iff]
  have aux : (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    aesop
  rw [← cartanMatrixIn_mul_diagonal_eq (S := S), Matrix.Nondegenerate.mul_iff_right aux,
    Matrix.nondegenerate_iff_det_ne_zero, ← (algebraMap S R).mapMatrix_apply,
    ← RingHom.map_det, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff] at hB
  rwa [Matrix.nondegenerate_iff_det_ne_zero]

section IsCrystallographic

variable [P.IsCrystallographic]

/-- The Cartan matrix of a crystallographic root pairing, with respect to a base `b`. -/
abbrev cartanMatrix :
    Matrix b.support b.support ℤ :=
  b.cartanMatrixIn ℤ

variable [CharZero R]

lemma cartanMatrix_apply_same (i : b.support) :
    b.cartanMatrix i i = 2 :=
  b.cartanMatrixIn_apply_same ℤ i

lemma cartanMatrix_apply_eq_zero_iff_pairing {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ P.pairing i j = 0 := by
  rw [cartanMatrix, cartanMatrixIn_def, ← (algebraMap_injective ℤ R).eq_iff,
    algebraMap_pairingIn, map_zero]

section neighbor

-- Probably shouldn't use.
lemma posForm_rootCombination {f g : b.support →₀ ℤ} (B : P.RootPositiveForm ℤ) :
    B.posForm (b.rootCombination ℤ f) (b.rootCombination ℤ g) =
    g.sum fun i m ↦ m • f.sum fun j n ↦ n • B.posForm (P.rootSpanMem ℤ j) (P.rootSpanMem ℤ i) := by
  simp only [rootCombination, LinearMap.map_finsupp_linearCombination,
    Finsupp.linearCombination_embDomain]
  simp only [Embedding.coe_subtype, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr ?_
  intro i hi
  congr 1
  exact LinearMap.finsupp_sum_apply f (fun i a ↦ a • B.posForm (P.rootSpanMem ℤ ↑i))
      (P.rootSpanMem ℤ ↑i)

-- may be superfluous.
lemma posForm_rootCombination_add {f₁ f₂ f₃ : b.support →₀ ℤ} (B : P.RootPositiveForm ℤ) :
    B.posForm (b.rootCombination ℤ (f₁ + f₂)) (b.rootCombination ℤ f₃) =
      B.posForm (b.rootCombination ℤ f₁) (b.rootCombination ℤ f₃) +
        B.posForm (b.rootCombination ℤ f₂) (b.rootCombination ℤ f₃) := by
  rw [b.rootCombination_add, LinearMap.BilinForm.add_left]


/-!
replace `posForm_rootCombination` with decomposition rules: given a subset `s` of `f.support`, split
`posForm` into the sum of the restriction of `f` to `s` and to the complement. Then, add a lemma
about evaluating on combinations with single support.

-/

lemma finsupp_base_posForm_pos [Fintype ι] [IsDomain R] {f : b.support →₀ ℤ} (hf : f ≠ 0) :
    0 < (P.posRootForm ℤ).posForm (b.rootCombination ℤ f) (b.rootCombination ℤ f) :=
  P.posRootForm_posForm_pos_of_ne_zero ℤ (b.rootCombination_ne_zero ℤ hf)

/-- The elements of a base, distinct from a particular element, that are not orthogonal to that
element. These correspond to adjacent vertices of a Dynkin diagram. -/
def neighbor (i : b.support) : Set b.support :=
  {j : b.support | b.cartanMatrix i j < 0}

omit [CharZero R] in
lemma neighbor_iff (i j : b.support) : j ∈ b.neighbor i ↔ P.pairingIn ℤ i j < 0 :=
  ⟨fun h ↦ h, fun h ↦ h⟩

lemma neighbor_symm [Finite ι] (i j : b.support) :
    j ∈ b.neighbor i ↔ i ∈ b.neighbor j := by
  simp only [neighbor_iff]
  exact pairingIn_lt_zero_iff P ℤ

lemma self_notMem_neighbor (i : b.support) : i ∉ b.neighbor i := by
  simp [neighbor]

lemma neq_of_neighbor {i j : b.support} (hj : j ∈ b.neighbor i) : i ≠ j :=
  fun h ↦ self_notMem_neighbor b j (h.symm ▸ hj)

lemma neighbor_disjoint (i : b.support) {s : Set b.support} (hs : s ⊆ (b.neighbor i)) :
    Disjoint s {i} :=
  fun _ h1 h2 _ h3 ↦ ((b.self_notMem_neighbor i) ((h2 h3) ▸ (hs (h1 h3)))).elim

lemma pairingIn_smul_rootLength_le [Fintype ι] {i j : b.support} (h : j ∈ b.neighbor i) :
    P.pairingIn ℤ i j • (P.posRootForm ℤ).rootLength j ≤ - (P.posRootForm ℤ).rootLength j := by
  rw [Int.neg_eq_neg_one_mul, ← smul_eq_mul]
  exact (smul_le_smul_iff_of_pos_right ((P.posRootForm ℤ).rootLength_pos j)).mpr
    (Int.add_le_zero_iff_le_neg.mp h)

lemma posForm_le_neg_rootLength_right [Fintype ι] {i j : b.support} (h : j ∈ b.neighbor i) :
  2 • (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤
    -(P.posRootForm ℤ).rootLength j := by
  rw [RootPositiveForm.two_smul_apply_rootSpanMem_rootSpanMem]
  exact b.pairingIn_smul_rootLength_le h

lemma posForm_le_neg_rootLength_left [Fintype ι] {i j : b.support} (h : j ∈ b.neighbor i) :
  2 • (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤
    -(P.posRootForm ℤ).rootLength i := by
  rw [← (P.posRootForm ℤ).isSymm_posForm.eq, RingHom.id_apply,
    RootPositiveForm.two_smul_apply_rootSpanMem_rootSpanMem]
  exact b.pairingIn_smul_rootLength_le ((neighbor_symm b i j).mp h)

end neighbor

variable [IsDomain R]

lemma cartanMatrix_apply_eq_zero_iff_symm {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ b.cartanMatrix j i = 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix_apply_eq_zero_iff_pairing, P.pairing_eq_zero_iff]

variable [Finite ι]

lemma cartanMatrix_le_zero_of_ne
    (i j : b.support) (h : i ≠ j) :
    b.cartanMatrix i j ≤ 0 :=
  b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

lemma cartanMatrix_mem_of_ne {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j ∈ ({-3, -2, -1, 0} : Set ℤ) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn ℤ i j ≤ 0 := b.cartanMatrix_le_zero_of_ne i j hij
  suffices P.pairingIn ℤ i j ≠ -4 by aesop
  by_contra contra
  replace contra : P.pairingIn ℤ j i = -1 ∧ P.pairingIn ℤ i j = -4 := ⟨by simp_all, contra⟩
  rw [pairingIn_neg_one_neg_four_iff] at contra
  refine (not_linearIndependent_iff.mpr ?_) b.linearIndepOn_root
  refine ⟨⟨{i, j}, by simpa⟩, Finsupp.single i (1 : R) + Finsupp.single j (2 : R), ?_⟩
  simp [contra, hij, hij.symm]

lemma cartanMatrix_eq_neg_chainTopCoeff {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = - P.chainTopCoeff j i := by
  rw [cartanMatrix, cartanMatrixIn_def, ← neg_eq_iff_eq_neg, b.chainTopCoeff_eq_of_ne j i hij.symm]

lemma cartanMatrix_apply_eq_zero_iff {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = 0 ↔ P.root i + P.root j ∉ range P.root := by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij, neg_eq_zero, Int.natCast_eq_zero,
    P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto

lemma abs_cartanMatrix_apply [DecidableEq ι] {i j : b.support} :
    |b.cartanMatrix i j| = (if i = j then 4 else 0) - b.cartanMatrix i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]
lemma cartanMatrix_map_abs [DecidableEq ι] :
    b.cartanMatrix.map abs = 4 - b.cartanMatrix := by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]

lemma cartanMatrix_nondegenerate
    {P : RootSystem ι R M N} [P.IsCrystallographic] (b : P.Base) :
    b.cartanMatrix.Nondegenerate :=
  let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate ℤ b

lemma nonpos_posForm {i j : b.support} (h : i ≠ j)
    (B : P.RootPositiveForm ℤ) :
    B.posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤ 0 := by
  suffices 2 • B.posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤ 0 by
    rw [two_nsmul] at this
    linarith
  rw [RootPositiveForm.two_smul_apply_rootSpanMem_rootSpanMem]
  exact smul_nonpos_of_nonpos_of_nonneg (b.cartanMatrix_le_zero_of_ne i j h)
    (RootPositiveForm.rootLength_pos B j).le

lemma not_neighbor_iff_orthogonal {i j : b.support} (h : i ≠ j) :
    j ∉ b.neighbor i ↔ P.IsOrthogonal i j := by
  simp only [neighbor, mem_setOf_eq, not_lt, IsOrthogonal]
  have hle := b.cartanMatrix_le_zero_of_ne i j h
  refine ⟨fun h ↦ ⟨(b.cartanMatrix_apply_eq_zero_iff_pairing).mp (by omega), ?_⟩,?_⟩
  · exact pairing_eq_zero_iff'.mp <| (b.cartanMatrix_apply_eq_zero_iff_pairing).mp (by omega)
  · exact fun h ↦ Int.le_of_eq ((b.cartanMatrix_apply_eq_zero_iff_pairing).mpr h.1).symm

lemma le_neg_one_posForm_of_neighbor [Fintype ι] {i j : b.support} (h : i ∈ b.neighbor j) :
    (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≤ -1 := by
  have hle := b.nonpos_posForm (b.neq_of_neighbor ((b.neighbor_symm j i).mp h)) (P.posRootForm ℤ)
  have : ¬ P.IsOrthogonal i j :=
    fun hO ↦ (b.not_neighbor_iff_orthogonal (b.neq_of_neighbor h)).mpr hO.symm h
  have hn : (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) ≠ 0 := by
    contrapose! this
    refine ((P.posRootForm ℤ).posForm_eq_zero_iff_IsOrthogonal i j).mp this
  omega

lemma posForm_of_pairing_neg_two [Fintype ι] {i j : b.support} (fi fj : ℤ)
    (hij : P.pairingIn ℤ i j = -2) :
    (P.posRootForm ℤ).posForm (b.rootCombination ℤ (Finsupp.single i fi + Finsupp.single j fj))
      (b.rootCombination ℤ (Finsupp.single i fi + Finsupp.single j fj)) =
      (fj * fj + fi * fi * 2 - fi * fj * 2) * (P.posRootForm ℤ).rootLength j := by
  rw [b.posForm_self_of_add (Finsupp.single i fi) (Finsupp.single j fj)
        (Finsupp.single i fi + Finsupp.single j fj) rfl]
  simp only [rootCombination_single, LinearMap.BilinForm.smul_left_of_tower,
    LinearMap.BilinForm.smul_right_of_tower]
  rw [← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength]
  have : P.root i ≠ -P.root j := b.root_ne_neg_of_ne i.2 j.2 (by aesop)
  have : (P.posRootForm ℤ).rootLength i = 2 * (P.posRootForm ℤ).rootLength j := by
    have hji := P.pairingIn_of_neg_two i j hij this
    have hp := (P.posRootForm ℤ).pairingIn_mul_eq_pairingIn_mul_swap i j
    rw [P.pairingIn_of_neg_two i j hij this, hij] at hp
    linarith
  rw [this, smul_comm 2 fj, smul_comm 2 fi,
    (P.posRootForm ℤ).two_smul_apply_rootSpanMem_rootSpanMem i j, hij]
  simp only [smul_eq_mul]
  linear_combination

lemma posForm_of_pairing_neg_three [Fintype ι] {i j : b.support} (fi fj : ℤ)
    (hij : P.pairingIn ℤ i j = -3) :
    (P.posRootForm ℤ).posForm (b.rootCombination ℤ (Finsupp.single i fi + Finsupp.single j fj))
      (b.rootCombination ℤ (Finsupp.single i fi + Finsupp.single j fj)) =
    (fj * fj + fi * fi * 3 - fi * fj * 3) * (P.posRootForm ℤ).rootLength j := by
  rw [b.posForm_self_of_add (Finsupp.single i fi) (Finsupp.single j fj)
        (Finsupp.single i fi + Finsupp.single j fj) rfl]
  simp only [rootCombination_single, LinearMap.BilinForm.smul_left_of_tower,
    LinearMap.BilinForm.smul_right_of_tower]
  have hlk (k : ι) : (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ k) (P.rootSpanMem ℤ k) =
    (P.posRootForm ℤ).rootLength k := rfl
  rw [hlk i, hlk j, smul_comm 2 fj, smul_comm 2 fi, P.rootLength_of_neg_three' i j hij,
    (P.posRootForm ℤ).two_smul_apply_rootSpanMem_rootSpanMem i j]
  simp only [smul_eq_mul, ← mul_assoc, hij, Int.reduceNeg, neg_mul, mul_neg]
  linear_combination

/-! Want some formulas for relating a Dynkin diagram `D` with `D + v` for an isolated vertex `v`.
-/

omit [IsDomain R] [Finite ι] in
lemma posForm_rootSpanMem_rootCombination_eq [Fintype ι] {f : b.support →₀ ℤ} {i : b.support} :
    ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i)) (b.rootCombination ℤ f) =
    ∑ j : b.support, f j • ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j)) := by
  rw [rootCombination_apply]
  simp only [Finsupp.sum, map_sum, Finset.univ_eq_attach]
  rw [Finset.sum_of_injOn]
  · exact fun i ↦ i
  · exact Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
  · intro i hi
    simp
  · intro i hi hni
    simp only [image_id', Finset.mem_coe, Finsupp.mem_support_iff, Decidable.not_not] at hni
    simp [hni]
  · intro j hj
    rw [LinearMap.BilinForm.smul_right_of_tower]

lemma posForm_rootSpanMem_rootCombination_le [Fintype ι] {f : b.support →₀ ℤ} {i j : b.support}
    (hi : i ∉ f.support) (hf : 0 ≤ f) (hj : 2 ≤ f j) (hij : j ∈ b.neighbor i) :
    ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i)) (b.rootCombination ℤ f) ≤
      -(P.posRootForm ℤ).rootLength i := by
  rw [posForm_rootSpanMem_rootCombination_eq, Finset.univ_eq_attach]
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_attach b.support i), ← Finset.add_sum_erase _ _
    (Finset.mem_erase.mpr ⟨(neq_of_neighbor b hij).symm, Finset.mem_attach b.support j⟩),
    Finsupp.notMem_support_iff.mp hi, zero_smul, zero_add]
  have : f j • ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i)) (P.rootSpanMem ℤ j) ≤
      -(P.posRootForm ℤ).rootLength i := by
    refine le_trans (Int.le_of_sub_nonpos ?_) (b.posForm_le_neg_rootLength_left hij)
    rw [Int.zsmul_eq_mul, Int.nsmul_eq_mul, Nat.cast_ofNat, ← sub_mul]
    exact Int.mul_nonpos_of_nonneg_of_nonpos (Int.sub_nonneg_of_le hj)
      (b.nonpos_posForm (b.neq_of_neighbor hij) (P.posRootForm ℤ))
  refine le_trans (Int.add_le_of_le_sub_left ?_) this
  rw [sub_self]
  refine Finset.sum_nonpos ?_
  intro k hk
  refine smul_nonpos_of_nonneg_of_nonpos (hf k) (nonpos_posForm b ?_ (P.posRootForm ℤ))
  simp only [Finset.mem_erase, Finset.mem_attach] at hk
  exact hk.2.1.symm

lemma posForm_apply_add_single_le [Fintype ι] {f g : b.support →₀ ℤ} {i j : b.support}
    (hi : i ∉ f.support) (hf : 0 ≤ f) (hfg : g = f + Finsupp.single i 1) (hj : 2 ≤ f j)
    (hxy : j ∈ b.neighbor i) :
    (P.posRootForm ℤ).posForm (b.rootCombination ℤ g) (b.rootCombination ℤ g) ≤
    (P.posRootForm ℤ).posForm (b.rootCombination ℤ f) (b.rootCombination ℤ f) -
      (P.posRootForm ℤ).rootLength i := by
  rw [hfg, rootCombination_add]
  simp only [map_add, LinearMap.add_apply, rootCombination_single, one_smul]
  have hfi := b.posForm_rootSpanMem_rootCombination_le hi hf hj hxy
  have : (P.posRootForm ℤ).posForm (b.rootCombination ℤ f) (P.rootSpanMem ℤ i) ≤
      -(P.posRootForm ℤ).rootLength i := by
    refine le_of_eq_of_le ?_ hfi
    rw [← (P.posRootForm ℤ).isSymm_posForm.eq (P.rootSpanMem ℤ i), RingHom.id_apply]
  rw [← RootPositiveForm.rootLength]
  linarith

-- start with two vertices, and build up inequalities.

lemma notMem_neighbor_left_of_pairing_neg_three [Fintype ι] {i j k : b.support}
    (hij : P.pairingIn ℤ i j = -3) (hjk : j ≠ k) : k ∉ b.neighbor i := by
  by_cases hik : i = k; · exact hik ▸ b.self_notMem_neighbor i
  have hnij : i ≠ j := by
    intro h
    have : P.pairingIn ℤ i j = 2 := h ▸ P.pairingIn_same ℤ j
    omega
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  let f : b.support →₀ ℤ := Finsupp.single i 2 + Finsupp.single j 3 + Finsupp.single k 1
  use f
  constructor
  · refine Finsupp.ne_iff.mpr ?_
    use i
    simp [f, Finsupp.single_eq_of_ne hnij.symm, Finsupp.single_eq_of_ne fun a ↦ hik a.symm]
  · rw [b.posForm_self_of_add (Finsupp.single i 2 + Finsupp.single j 3) (Finsupp.single k 1) f rfl,
      b.posForm_of_pairing_neg_three 2 3 hij]
    simp only [Int.reduceMul, Int.reduceAdd, Int.reduceSub, rootCombination_single,
      one_smul, b.rootCombination_add, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    rw [smul_add, two_smul]
    have (i j : ι) :
        (2 : ℤ) * ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i)) (P.rootSpanMem ℤ j) =
        P.pairingIn ℤ i j • (P.posRootForm ℤ).rootLength j := by
      simpa using (P.posRootForm ℤ).two_smul_apply_rootSpanMem_rootSpanMem i j
    nth_rw 1 [this i k]
    rw [← (P.posRootForm ℤ).isSymm_posForm.eq (P.rootSpanMem ℤ k) (P.rootSpanMem ℤ i),
      RingHom.id_apply, this k i, ← add_assoc]
    refine Int.add_nonpos ?_ ?_
    · rw [add_rotate, ← add_assoc, add_assoc _ _ (3 * (P.posRootForm ℤ).rootLength ↑j)]
      refine Int.add_nonpos ?_ ?_
      · dsimp [RootPositiveForm.rootLength]
        nth_rw 1 [← one_smul ℤ ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ k) (P.rootSpanMem ℤ k))]
        rw [← smul_eq_mul, ← add_smul]
        refine smul_nonpos_of_nonpos_of_nonneg ?_ (zero_le_posForm P ℤ (P.rootSpanMem ℤ k))
        exact Int.add_le_zero_iff_le_neg'.mpr <| Int.add_le_zero_iff_le_neg.mp hp
      · rw [← P.rootLength_of_neg_three' i j hij]
        nth_rw 2 [← one_smul ℤ ((P.posRootForm ℤ).rootLength i)]
        rw [← add_smul]
        refine smul_nonpos_of_nonpos_of_nonneg ?_ (le_of_lt <| (P.posRootForm ℤ).rootLength_pos i)
        exact Int.add_one_le_of_lt <| (pairingIn_lt_zero_iff P ℤ).mp hp
    · refine Left.nsmul_nonpos ?_ 2
      refine Int.mul_nonpos_of_nonneg_of_nonpos (by simp) (nonpos_posForm b hjk (P.posRootForm ℤ))

lemma notMem_neighbor_right_of_pairing_neg_three [Fintype ι] {i j k : b.support}
    (hij : P.pairingIn ℤ i j = -3) (hik : i ≠ k) : k ∉ b.neighbor j := by
  by_cases hjk : j = k; · exact hjk ▸ b.self_notMem_neighbor j
  have hnij : i ≠ j := by
    intro h
    rw [h] at hij
    have := pairingIn_same P ℤ j
    omega
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  let f : b.support →₀ ℤ := Finsupp.single i 1 + Finsupp.single j 2 + Finsupp.single k 1
  use f
  constructor
  · refine Finsupp.ne_iff.mpr ?_
    use j
    simp [f, Finsupp.single_eq_of_ne hnij, Finsupp.single_eq_of_ne fun a ↦ hjk a.symm]
  · rw [b.posForm_self_of_add (Finsupp.single i 1 + Finsupp.single j 2) (Finsupp.single k 1) f rfl,
      b.posForm_of_pairing_neg_three 1 2 hij]
    simp only [Int.reduceMul, mul_one, one_mul, Int.reduceAdd, Int.reduceSub,
      rootCombination_single, one_smul, b.rootCombination_add, nsmul_eq_mul, Nat.cast_ofNat]
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    have (i j : ι) :
        (2 : ℤ) * ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i)) (P.rootSpanMem ℤ j) =
        P.pairingIn ℤ i j • (P.posRootForm ℤ).rootLength j := by
      simpa using (P.posRootForm ℤ).two_smul_apply_rootSpanMem_rootSpanMem i j
    rw [mul_add, this i k, two_mul]
    nth_rw 1 [← (P.posRootForm ℤ).isSymm_posForm.eq (P.rootSpanMem ℤ k) (P.rootSpanMem ℤ j)]
    rw [RingHom.id_apply, this k j, this j k, ← RootPositiveForm.rootLength]
    have : 0 < (P.posRootForm ℤ).rootLength k := (P.posRootForm ℤ).rootLength_pos k
    have hk1 := pairingIn_smul_rootLength_le b hp
    have hj1 := pairingIn_smul_rootLength_le b ((neighbor_symm b j k).mp hp)
    have hik : P.pairingIn ℤ i k • (P.posRootForm ℤ).rootLength k ≤ 0 := by
      refine smul_nonpos_of_nonpos_of_nonneg ?_ (Int.le_of_lt <| (P.posRootForm ℤ).rootLength_pos k)
      by_cases hn : k ∈ b.neighbor i
      · exact Int.le_of_lt hn
      · refine le_of_eq <| (FaithfulSMul.algebraMap_injective ℤ R) ?_
        rw [algebraMap_pairingIn, RingHom.map_zero]
        exact ((not_neighbor_iff_orthogonal b hik).mp hn).1
    linarith

omit [IsDomain R] in
lemma isOrthogonal_of_neighbor [IsDomain R] [Fintype ι] {i j k : b.support} (hj : j ∈ b.neighbor i)
    (hk : k ∈ b.neighbor i) (hjk : j ≠ k) :
    P.IsOrthogonal j k := by
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  have hnij : i ≠ j := neq_of_neighbor b hj
  have hik : i ≠ k := neq_of_neighbor b hk
  let f : b.support →₀ ℤ := Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1
  use f
  constructor
  · refine Finsupp.ne_iff.mpr ?_
    use i
    simp [f, Finsupp.single_eq_of_ne hnij.symm, Finsupp.single_eq_of_ne fun a ↦ hik a.symm]
  · rw [b.posForm_self_of_add (Finsupp.single i 1 + Finsupp.single j 1) (Finsupp.single k 1) f rfl,
      b.posForm_self_of_add (Finsupp.single i 1) (Finsupp.single j 1) _ rfl]
    have := (P.posRootForm ℤ).pairingIn_mul_eq_pairingIn_mul_swap i j
    simp only [rootCombination_add, rootCombination_single, one_smul, LinearMap.BilinForm.add_left]
    rw [smul_add, ← (P.posRootForm ℤ).isSymm_posForm.eq (P.rootSpanMem ℤ k) (P.rootSpanMem ℤ i),
      RingHom.id_apply]
    simp only [RootPositiveForm.two_smul_apply_rootSpanMem_rootSpanMem]
    have : k ∈ b.neighbor j := by
      contrapose! hp
      rwa [← b.not_neighbor_iff_orthogonal hjk]
    have hk1 := pairingIn_smul_rootLength_le b this
    have hj1 := pairingIn_smul_rootLength_le b hj
    have hi1 := pairingIn_smul_rootLength_le b ((neighbor_symm b i k).mp hk)
    rw [← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength]
    linarith

/-!
lemma notMem_neighbor_of_neighbor_neighbor_neighbor' [Fintype ι] {i j₁ j₂ j₃ k : b.support}
    (hi₁ : j₁ ∈ b.neighbor i) (hi₂ : j₂ ∈ b.neighbor i) (hi₃ : j₃ ∈ b.neighbor i) (h₁₂ : j₁ ≠ j₂)
    (h₂₃ : j₂ ≠ j₃) (h₁₃ : j₁ ≠ j₃) (hk₁ : k ≠ j₁) (hk₂ : k ≠ j₂) (hk₃ : k ≠ j₃) :
    k ∉ b.neighbor i := by
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  let f : b.support →₀ ℤ := Finsupp.single i 2 + Finsupp.single j₁ 1 + Finsupp.single j₂ 1 +
    Finsupp.single j₃ 1 + Finsupp.single k 1
  use f
  constructor
  · refine Finsupp.ne_iff.mpr ?_
    use i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.coe_zero, f]
    simp [Finsupp.single_eq_of_ne (neq_of_neighbor b hi₁).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hi₂).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hi₃).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hp).symm]
  · let f₁ : b.support →₀ ℤ := Finsupp.single i 2 + Finsupp.single j₁ 1 + Finsupp.single j₂ 1 +
      Finsupp.single j₃ 1
    suffices (P.posRootForm ℤ).posForm (b.rootCombination ℤ f₁) (b.rootCombination ℤ f₁) ≤
        (P.posRootForm ℤ).rootLength i by
      have hk : k ∉ f₁.support := by
        simp [f₁, Finsupp.single_eq_of_ne hk₂.symm, Finsupp.single_eq_of_ne hk₁.symm,
          Finsupp.single_eq_of_ne hk₃.symm, Finsupp.single_eq_of_ne (neq_of_neighbor b hp)]
      have hf₁ : 0 ≤ f₁ := by
        refine add_nonneg ?_ ?_
        · refine add_nonneg ?_ ?_
          · refine add_nonneg ?_ ?_
            · exact Finsupp.single_nonneg.mpr <| Int.zero_le_ofNat 2
            · exact Finsupp.single_nonneg.mpr Int.one_nonneg
          · exact Finsupp.single_nonneg.mpr Int.one_nonneg
        · exact Finsupp.single_nonneg.mpr Int.one_nonneg
      have := b.posForm_apply_add_single_le hk hf₁ rfl (j := i)


lemma notMem_neighbor_of_neighbor_neighbor_neighbor [Fintype ι] {i j₁ j₂ j₃ k : b.support}
    (hi₁ : j₁ ∈ b.neighbor i) (hi₂ : j₂ ∈ b.neighbor i) (hi₃ : j₃ ∈ b.neighbor i) (h₁₂ : j₁ ≠ j₂)
    (h₂₃ : j₂ ≠ j₃) (h₁₃ : j₁ ≠ j₃) (hk₁ : k ≠ j₁) (hk₂ : k ≠ j₂) (hk₃ : k ≠ j₃) :
    k ∉ b.neighbor i := by
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  let f : b.support →₀ ℤ := Finsupp.single i 2 + Finsupp.single j₁ 1 + Finsupp.single j₂ 1 +
    Finsupp.single j₃ 1 + Finsupp.single k 1
  use f
  constructor
  · refine Finsupp.ne_iff.mpr ?_
    use i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.coe_zero, f]
    simp [Finsupp.single_eq_of_ne (neq_of_neighbor b hi₁).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hi₂).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hi₃).symm,
      Finsupp.single_eq_of_ne (neq_of_neighbor b hp).symm]
  · rw [b.posForm_self_of_add (Finsupp.single i 2 + Finsupp.single j₁ 1 + Finsupp.single j₂ 1 +
        Finsupp.single j₃ 1) (Finsupp.single k 1) f rfl,
      b.posForm_self_of_add (Finsupp.single i 2 + Finsupp.single j₁ 1 + Finsupp.single j₂ 1)
        (Finsupp.single j₃ 1) _ rfl,
      b.posForm_self_of_add (Finsupp.single i 2 + Finsupp.single j₁ 1) (Finsupp.single j₂ 1) _ rfl,
      b.posForm_self_of_add (Finsupp.single i 2) (Finsupp.single j₁ 1) _ rfl]
    simp only [rootCombination_add, rootCombination_single, one_smul, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, two_mul, smul_add]
    rw [← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength,
      ← RootPositiveForm.rootLength, ← RootPositiveForm.rootLength]
    have hij₁ := b.posForm_le_neg_rootLength_right hi₁
    have hij₂ := b.posForm_le_neg_rootLength_right hi₂
    have hij₃ := b.posForm_le_neg_rootLength_right hi₃
    have hik := b.posForm_le_neg_rootLength_right hp
    have hj₁i := b.posForm_le_neg_rootLength_right ((neighbor_symm b i j₁).mp hi₁)
    have hj₂i := b.posForm_le_neg_rootLength_right ((neighbor_symm b i j₂).mp hi₂)
    have hj₃i := b.posForm_le_neg_rootLength_right ((neighbor_symm b i j₃).mp hi₃)
    have hki := b.posForm_le_neg_rootLength_right ((neighbor_symm b i k).mp hp)
    have hij₁' := b.posForm_le_neg_rootLength_left hi₁
    have hij₂' := b.posForm_le_neg_rootLength_left hi₂
    have hij₃' := b.posForm_le_neg_rootLength_left hi₃
    have hik' := b.posForm_le_neg_rootLength_left hp
    have hj₁i' := b.posForm_le_neg_rootLength_left ((neighbor_symm b i j₁).mp hi₁)
    have hj₂i' := b.posForm_le_neg_rootLength_left ((neighbor_symm b i j₂).mp hi₂)
    have hj₃i' := b.posForm_le_neg_rootLength_left ((neighbor_symm b i j₃).mp hi₃)
    have hki' := b.posForm_le_neg_rootLength_left ((neighbor_symm b i k).mp hp)
    have hj₁₂ := nonpos_posForm b h₁₂ (P.posRootForm ℤ)
    have hj₂₁ := nonpos_posForm b h₁₂.symm (P.posRootForm ℤ)
    have hj₁₃ := nonpos_posForm b h₁₃ (P.posRootForm ℤ)
    have hj₃₁ := nonpos_posForm b h₁₃.symm (P.posRootForm ℤ)
    have hj₂₃ := nonpos_posForm b h₂₃ (P.posRootForm ℤ)
    have hj₃₂ := nonpos_posForm b h₂₃.symm (P.posRootForm ℤ)
    have hkj₁ := nonpos_posForm b hk₁ (P.posRootForm ℤ)
    have hj₁k := nonpos_posForm b hk₁.symm (P.posRootForm ℤ)
    have hkj₂ := nonpos_posForm b hk₂ (P.posRootForm ℤ)
    have hj₂k := nonpos_posForm b hk₂.symm (P.posRootForm ℤ)
    have hkj₃ := nonpos_posForm b hk₃ (P.posRootForm ℤ)
    have hj₃k := nonpos_posForm b hk₃.symm (P.posRootForm ℤ)
    have hi := (P.posRootForm ℤ).rootLength_pos i
    have hj₁ := (P.posRootForm ℤ).rootLength_pos j₁
    have hj₂ := (P.posRootForm ℤ).rootLength_pos j₂
    have hj₃ := (P.posRootForm ℤ).rootLength_pos j₃
    have hk := (P.posRootForm ℤ).rootLength_pos k

    --linarith    --fails still
    sorry

lemma neighbor_card_le_three [IsDomain R] [Fintype ι] (i : b.support) :
    encard (b.neighbor i) ≤ 3 := by
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  have : 4 ≤ encard (b.neighbor i) := by
    contrapose! hp
    exact Order.le_of_lt_succ hp
  have : ∃ S : Set b.support, S ⊆ (b.neighbor i) ∧ encard S = 4 := by
    apply exists_subset_encard_eq this
  obtain ⟨S, hS1, hS2⟩ := this
  have _ : Finite (Set.indicator S (fun i ↦ (1 : ℤ))).support := by
    exact Subtype.finite
  have hSi : Disjoint S {i} := b.neighbor_disjoint i hS1
  let fS := Finsupp.ofSupportFinite (Set.indicator S (fun i ↦ (1 : ℤ))) Subtype.finite
  have : fS.support = S := by
    ext j
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
    simp
  let f := Finsupp.single i (1 : ℤ) + fS
  have : f = Finsupp.ofSupportFinite (Set.indicator (S ∪ {i}) (fun i ↦ (1 : ℤ)))
      (toFinite (Function.support ((S ∪ {i}).indicator fun i ↦ 1))) := by
    ext j
    by_cases hj : j ∈ S ∪ {i}
    · rw [Finsupp.add_apply, indicator_union_of_disjoint hSi fun i ↦ 1, Finsupp.ofSupportFinite_coe,
        Finsupp.ofSupportFinite_coe, Finsupp.single_eq_set_indicator, Int.add_comm]
    · rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe,
        Finsupp.single_eq_set_indicator, indicator_of_notMem hj]
      rw [mem_union] at hj
      push_neg at hj
      rw [indicator_of_notMem hj.1, indicator_of_notMem hj.2, Int.add_zero]
  have hfsup : f.support = S ∪ {i} := by
    ext j
    rw [this, Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
    simp
    tauto
  use f
  constructor
  · have : i ∈ f.support := by
      rw [← Finset.mem_coe, hfsup]
      exact mem_union_right S rfl
    rw [Finsupp.mem_support_iff] at this
    exact ne_of_apply_ne DFunLike.coe fun a ↦ this (congrFun a i)
  · dsimp only [rootCombination, Finsupp.linearCombination, Finsupp.coe_lsum,
      LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, SetLike.mk_smul_mk]
    simp only [posRootForm_eq, this, union_singleton]
    sorry

    --have := Fintype.ofFinite S
    --have hNS : Nat.card S = 4 := by
      --have := hS.2
      --rw [Nat.card_eq_fintype_card]
      --rw [encard_eq_coe_toFinset_card, toFinset_card] at this
      --exact ENat.coe_inj.mp this

lemma neg_one_le_cartanMatrix_row_sum [IsDomain R] [Fintype ι] (i : b.support) [Fintype b.support] :
    -1 ≤ ∑ j : b.support, b.cartanMatrix i j := by
  have hp (x : P.rootSpan ℤ) (hz : x ≠ 0) := P.posRootForm_posForm_pos_of_ne_zero ℤ hz
  contrapose! hp
  let nb (i : b.support): Set b.support := {j : b.support | b.cartanMatrix i j < 0}


  sorry
-/

/-- A characterisation of the connectedness of the Dynkin diagram for irreducible root pairings. -/
lemma induction_on_cartanMatrix [P.IsReduced] [P.IsIrreducible]
    (p : b.support → Prop) {i j : b.support} (hi : p i)
    (hp : ∀ i j, p i → b.cartanMatrix j i ≠ 0 → p j) :
    p j := by
  have _i : Nontrivial M := ⟨P.root i, 0, P.ne_zero i⟩
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
  have hq₀ : q ≠ ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span <| by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k ∈ q ↔ p k := by
    refine ⟨fun hk ↦ ?_, fun hk ↦ subset_span <| by simpa⟩
    contrapose! hk
    exact b.linearIndepOn_root.linearIndependent.notMem_span_image hk
  have hq_notMem (k : b.support) (hk : P.root k ∉ q) : q ≤ LinearMap.ker (P.coroot' k) := by
    refine fun x hx ↦ LinearMap.mem_ker.mpr ?_
    contrapose! hk
    rw [hq_mem]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ : ∃ l : b.support, p l ∧ P.root l = x := by simp_all
      replace hk : b.cartanMatrix k l ≠ 0 := by
        rwa [ne_eq, cartanMatrix_apply_eq_zero_iff_symm, cartanMatrix_apply_eq_zero_iff_pairing]
      tauto
    | zero => simp_all
    | add x y hx hy hx' hy' =>
      replace hk : P.coroot' k x ≠ 0 ∨ P.coroot' k y ≠ 0 := by by_contra! contra; simp_all
      tauto
    | smul a x hx hx' => simp_all
  have hq : ∀ k, q ∈ invtSubmodule (P.reflection k) := by
    rw [← b.forall_mem_support_invtSubmodule_iff]
    refine fun k hkb ↦ (mem_invtSubmodule _).mpr fun x hx ↦ ?_
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply]
    apply q.sub_mem hx
    by_cases hk : P.root k ∈ q
    · exact q.smul_mem _ hk
    · replace hk : P.coroot' k x = 0 := hq_notMem ⟨k, hkb⟩ hk hx
      simp [hk]
  simp [← hq_mem, IsIrreducible.eq_top_of_invtSubmodule_reflection q hq hq₀]

open scoped Matrix in
lemma injective_pairingIn {P : RootSystem ι R M N} [P.IsCrystallographic] (b : P.Base) :
    Injective (fun i (k : b.support) ↦ P.pairingIn ℤ i k) := by
  classical
  intro i j hij
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  let f' : b.support → ℤ := f ∘ (↑)
  let g' : b.support → ℤ := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq, hf, hg]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    replace this : f k = g k := congr_fun this ⟨k, hk⟩
    rw [this]
  replace hf : (fun k : b.support ↦ P.pairingIn ℤ i k) = f' ᵥ* b.cartanMatrix := by
    suffices ∀ k, P.pairingIn ℤ i k = ∑ l ∈ b.support, f l * P.pairingIn ℤ l k by
      ext; simp [f', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k ↦ algebraMap_injective ℤ R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hf]
  replace hg : (fun k : b.support ↦ P.pairingIn ℤ j k) = g' ᵥ* b.cartanMatrix := by
    suffices ∀ k, P.pairingIn ℤ j k = ∑ l ∈ b.support, g l * P.pairingIn ℤ l k by
      ext; simp [g', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k ↦ algebraMap_injective ℤ R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hg]
  suffices Injective fun v ↦ v ᵥ* b.cartanMatrix from this <| by simpa [← hf, ← hg]
  rw [Matrix.vecMul_injective_iff]
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

lemma exists_mem_span_pairingIn_ne_zero_and_pairwise_ne
    {K : Type*} [Field K] [CharZero K] [Module K M] [Module K N]
    {P : RootSystem ι K M N} [P.IsCrystallographic] (b : P.Base) :
    ∃ d ∈ span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K)),
      (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) := by
  set p := span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K))
  let f : ι ⊕ {(i, j) : ι × ι | i ≠ j} → Module.Dual K (ι → K) := Sum.elim
    LinearMap.proj (fun x ↦ LinearMap.proj (R := K) (φ := fun _ ↦ K) x.1.1 - LinearMap.proj x.1.2)
  suffices ∃ d ∈ p, ∀ i, f i d ≠ 0 by
    obtain ⟨d, hp, hf⟩ := this
    refine ⟨d, hp, fun i ↦ hf (Sum.inl i), fun i j h ↦ ?_⟩
    simpa [f, sub_eq_zero] using hf (Sum.inr ⟨⟨i, j⟩, h⟩)
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists p f
  rintro (i | ⟨⟨i, j⟩, h : i ≠ j⟩)
  · obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
    refine ⟨fun i ↦ P.pairingIn ℤ i j, subset_span ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
    simpa [f, ne_eq, Int.cast_eq_zero]
  · obtain ⟨k, hk, hk'⟩ : ∃ k ∈ b.support, P.pairingIn ℤ i k ≠ P.pairingIn ℤ j k := by
      contrapose! h
      apply b.injective_pairingIn
      aesop
    simpa [f, sub_eq_zero] using ⟨fun i ↦ P.pairingIn ℤ i k, subset_span ⟨⟨k, hk⟩, rfl⟩, by simpa⟩

end IsCrystallographic

end RootPairing.Base
