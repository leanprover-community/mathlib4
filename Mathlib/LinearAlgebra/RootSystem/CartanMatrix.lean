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

lemma cartanMatrix_eq_neg_chainTopCoeff [Finite ι] [IsDomain R] {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = - P.chainTopCoeff j i := by
  rw [cartanMatrix, cartanMatrixIn_def, ← neg_eq_iff_eq_neg, ← b.chainTopCoeff_eq_of_ne hij.symm]

lemma cartanMatrix_apply_eq_zero_iff [Finite ι] [IsDomain R] {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j = 0 ↔ P.root i + P.root j ∉ range P.root := by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij, neg_eq_zero, Int.natCast_eq_zero,
    P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto

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

open Module.End (invtSubmodule mem_invtSubmodule)
open MulAction (orbit mem_orbit_self mem_orbit_iff)
open Submodule (span subset_span)
open FaithfulSMul (algebraMap_injective)

variable [NoZeroSMulDivisors ℤ M] [Fintype ι] [P.IsReduced]

-- TODO Move (obviously)
omit [CharZero R] in
lemma foo [P.IsIrreducible] (q : Submodule R M)
    (h₁ : ∀ i ∈ b.support, q ∈ invtSubmodule (P.reflection i)) (h₂ : q ≠ ⊥) : q = ⊤ := by
  nontriviality M
  suffices ∀ i, q ∈ invtSubmodule (P.reflection i) from
    IsIrreducible.eq_top_of_invtSubmodule_reflection q this h₂
  intro i
  letI := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction'' i (by aesop) h₁ ?_
  clear i
  intro i j hi hj
  have : P.reflection (P.reflectionPerm j i) =
      P.reflection j * P.reflection i * P.reflection j := by
    ext x; simp [coreflection_apply, reflection_apply]; module -- TODO Is this really missing!?
  rw [this]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (h₁ j hj) hi) (h₁ j hj)

/- Should we include this stronger statement:
lemma foo' (q : Submodule R M) :
    (∀ i ∈ b.support, q ∈ invtSubmodule (P.reflection i)) ↔
      (∀ i, q ∈ invtSubmodule (P.reflection i)) := by
  sorry
-/

/-- A characterisation of the connectedness of the Dynkin diagram for irreducible root pairings. -/
lemma induction_on [IsDomain R] [P.IsIrreducible]
    (p : b.support → Prop) {i j : b.support} (hi : p i)
    (hp : ∀ i j, p i → b.cartanMatrix j i ≠ 0 → p j) :
    p j := by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
  have hq_mem (k : b.support) : P.root k ∈ q ↔ p k := by
    refine ⟨fun hk ↦ ?_, fun hk ↦ subset_span <| by simpa⟩
    contrapose! hk
    exact b.linearIndepOn_root.linearIndependent.notMem_span_image hk
  have hq_mem' {k : b.support} (hk : P.root k ∉ q) : q ≤ LinearMap.ker (P.coroot' k) := by
    intro x hx
    rw [LinearMap.mem_ker]
    contrapose! hk
    rw [hq_mem]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ : ∃ l : b.support, p l ∧ P.root l = x := by aesop
      replace hk : b.cartanMatrix k l ≠ 0 := by
        -- TODO Should probably break this out as convenience lemma:
        -- `b.cartanMatrix k l ≠ 0 ↔ b.cartanMatrix l k ≠ 0`
        rwa [cartanMatrix, cartanMatrixIn_def, ← (algebraMap_injective ℤ R).ne_iff,
          algebraMap_pairingIn, map_zero, ne_eq, pairing_eq_zero_iff']
      tauto
    | zero => aesop
    | add x y hx hy hx' hy' =>
      replace hk : P.coroot' k x ≠ 0 ∨ P.coroot' k y ≠ 0 := by by_contra! contra; aesop
      tauto
    | smul a x hx hx' =>
      replace hk : P.coroot' k x ≠ 0 := by contrapose! hk; simp [hk]
      tauto
  have hq (k : ι) (hkb : k ∈ b.support) : q ∈ invtSubmodule (P.reflection k) := by
    rw [mem_invtSubmodule]
    intro x hx
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply]
    apply q.sub_mem hx
    by_cases hk : P.root k ∈ q
    · exact q.smul_mem _ hk
    · replace hk : P.coroot' k x = 0 := hq_mem' (k := ⟨k, hkb⟩) hk hx
      simp [hk]
  have hq₀ : q ≠ ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span <| by simpa, P.ne_zero i⟩
  simp [← hq_mem, b.foo q hq hq₀]

end IsCrystallographic

end RootPairing.Base
