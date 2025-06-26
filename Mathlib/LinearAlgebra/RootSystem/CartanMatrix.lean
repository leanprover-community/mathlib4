/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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

-/

noncomputable section

open Function Set

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
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] [Fintype b.support] :
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

lemma cartanMatrix_zero_iff (i j : b.support) :
    b.cartanMatrix i j = 0 ↔ P.pairing i j = 0 := by
  rw [cartanMatrix, cartanMatrixIn, Matrix.of_apply, ← P.algebraMap_pairingIn ℤ]
  exact (FaithfulSMul.algebraMap_eq_zero_iff ℤ R).symm

lemma cartanMatrix_le_zero_of_ne [Finite ι] [IsDomain R]
    (i j : b.support) (h : i ≠ j) :
    b.cartanMatrix i j ≤ 0 :=
  b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

lemma cartanMatrix_mem_of_ne [Finite ι] [IsDomain R] {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j ∈ ({-3, -2, -1, 0} : Set ℤ) := by
  have := P.reflexive_left
  have := P.reflexive_right
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn ℤ i j ≤ 0 := b.cartanMatrix_le_zero_of_ne i j hij
  suffices P.pairingIn ℤ i j ≠ -4 by aesop
  by_contra contra
  replace contra : P.pairingIn ℤ j i = -1 ∧ P.pairingIn ℤ i j = -4 := ⟨by aesop, contra⟩
  rw [pairingIn_neg_one_neg_four_iff] at contra
  refine (not_linearIndependent_iff.mpr ?_) b.linearIndepOn_root
  refine ⟨⟨{i, j}, by simpa⟩, Finsupp.single i (1 : R) + Finsupp.single j (2 : R), ?_⟩
  simp [contra, hij, hij.symm]

lemma abs_cartanMatrix_apply [Finite ι] [DecidableEq ι] [IsDomain R] {i j : b.support} :
    |b.cartanMatrix i j| = (if i = j then 4 else 0) - b.cartanMatrix i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]
lemma cartanMatrix_map_abs [DecidableEq ι] [Finite ι] [IsDomain R] :
    b.cartanMatrix.map abs = 4 • 1 - b.cartanMatrix := by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]

lemma cartanMatrix_nondegenerate [Finite ι] [IsDomain R]
    {P : RootSystem ι R M N} [P.IsCrystallographic] (b : P.Base) :
    b.cartanMatrix.Nondegenerate :=
  let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate ℤ b

/-!
lemma posForm_rootCombination {f g : b.support →₀ ℤ} (B : P.RootPositiveForm S) :
    B.posForm (b.rootCombination ℤ f) (b.rootCombination ℤ g) =
      ∑ f.sum fun i ↦ , ∑ g.sum, B.posForm
-/

lemma finsupp_base_posForm_pos [Fintype ι] [IsDomain R] {f : b.support →₀ ℤ} (hf : f ≠ 0) :
    0 < (P.posRootForm ℤ).posForm (b.rootCombination ℤ f) (b.rootCombination ℤ f) :=
  P.posRootForm_posForm_pos_of_ne_zero ℤ (b.rootCombination_ne_zero ℤ hf)

/-- The elements of a base, distinct from a particular element, that are not orthogonal to that
element. These correspond to adjacent vertices of a Dynkin diagram. -/
def neighbor (i : b.support) : Set b.support :=
  {j : b.support | b.cartanMatrix i j < 0}

lemma neighbor_symm [Finite ι] (i j : b.support) :
    j ∈ b.neighbor i ↔ i ∈ b.neighbor j := by
  simp [neighbor, cartanMatrix, cartanMatrixIn, mem_setOf_eq]
  obtain rfl | hij := eq_or_ne i j
  · exact gt_iff_lt
  · exact pairingIn_lt_zero_iff P ℤ

lemma not_neighbor_iff_orthogonal [Finite ι] [IsDomain R] {i j : b.support} (h : i ≠ j) :
    j ∉ b.neighbor i ↔ P.IsOrthogonal i j := by
  simp only [neighbor, mem_setOf_eq, not_lt, IsOrthogonal]
  have hle := b.cartanMatrix_le_zero_of_ne i j h
  refine ⟨fun h ↦ ⟨(b.cartanMatrix_zero_iff i j).mp (by omega), ?_⟩,?_⟩
  · exact pairing_eq_zero_iff'.mp <| (b.cartanMatrix_zero_iff i j).mp (by omega)
  · exact fun h ↦ Int.le_of_eq ((b.cartanMatrix_zero_iff i j).mpr h.1).symm

lemma self_notMem_neighbor (i : b.support) : i ∉ b.neighbor i := by simp [neighbor]

lemma neighbor_disjoint (i : b.support) {s : Set b.support} (hs : s ⊆ (b.neighbor i)) :
    Disjoint s {i} :=
  fun _ h1 h2 _ h3 ↦ ((b.self_notMem_neighbor i) ((h2 h3) ▸ (hs (h1 h3)))).elim

/-!
lemma neighbor_isOrthogonal [IsDomain R] [Fintype ι] {i j k : b.support} (hj : j ∈ b.neighbor i)
    (hk : k ∈ b.neighbor i) :
    P.IsOrthogonal j k := by
  have hp {f : b.support →₀ ℤ} (hf : f ≠ 0) := b.finsupp_base_posForm_pos hf
  contrapose! hp
  let S := ({i, j, k}: Set b.support)
  let f := Finsupp.ofSupportFinite (Set.indicator S (fun i ↦ (1 : ℤ)))
      (toFinite (Function.support (S.indicator fun i ↦ 1)))
  use f
  constructor
  · have : f i = (1 : ℤ) := by
      rw [Finsupp.ofSupportFinite_coe, indicator_apply_eq_self]
      exact fun h ↦ (h (mem_insert i {j, k})).elim
    apply Finsupp.ne_iff.mpr
    use i
    simp [this]
  · simp [rootCombination, Finsupp.linearCombination]

    let x := (P.posRootForm ℤ).rootLength i
    have := (P.posRootForm ℤ).pairingIn_mul_eq_pairingIn_mul_swap i j
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
  obtain ⟨S, hS⟩ := this
  have _ : Finite (Set.indicator S (fun i ↦ (1 : ℤ))).support := by
    exact Subtype.finite
  have hSi : Disjoint S {i} := b.neighbor_disjoint i hS.1
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

end IsCrystallographic

end RootPairing.Base
