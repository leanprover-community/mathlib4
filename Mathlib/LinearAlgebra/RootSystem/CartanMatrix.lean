/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
* `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
  respect to a base `b`.
* `RootPairing.Base.cartanMatrix_nondegenerate`: the Cartan matrix is non-degenerate.
* `RootPairing.Base.induction_on_cartanMatrix`: an induction principle expressing the connectedness
  of the Dynkin diagram of an irreducible root pairing.
* `RootPairing.Base.equivOfCartanMatrixEq`: a root system is determined by its Cartan matrix.

-/

@[expose] public section

noncomputable section

open FaithfulSMul (algebraMap_injective)
open Function Set Matrix
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
lemma cartanMatrixIn_mul_diagonal_eq {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S]
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] :
    (b.cartanMatrixIn S).map (algebraMap S R) *
      (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)) =
      (2 : R) • B.form.toMatrix b.toWeightBasis := by
  ext
  simp [B.two_mul_apply_root_root]

lemma cartanMatrixIn_nondegenerate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] [Fintype ι] [P.IsAnisotropic]
    (b : P.Base) :
    (b.cartanMatrixIn S).Nondegenerate := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • B.form.toMatrix b.toWeightBasis).Nondegenerate := by
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

variable [IsDomain R]

lemma cartanMatrix_apply_eq_zero_iff_symm {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ b.cartanMatrix j i = 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
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
  rw [cartanMatrix, cartanMatrixIn_def, ← neg_eq_iff_eq_neg, ← b.chainTopCoeff_eq_of_ne hij.symm]

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
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    b.cartanMatrix.Nondegenerate :=
  let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate ℤ b

/-- A characterisation of the connectedness of the Dynkin diagram for irreducible root pairings. -/
lemma induction_on_cartanMatrix [P.IsReduced] [P.IsIrreducible]
    (p : b.support → Prop) {i j : b.support} (hi : p i)
    (hp : ∀ i j, p i → b.cartanMatrix j i ≠ 0 → p j) :
    p j := by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
  have hq₀ : q ≠ ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span <| by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k ∈ q ↔ p k := by
    refine ⟨fun hk ↦ ?_, fun hk ↦ subset_span <| by simpa⟩
    contrapose hk
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

-- TODO Derive from `LinearIndependent.injective`
open scoped Matrix in
lemma injective_pairingIn {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    (b : P.Base) :
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
    {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
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

section Uniqueness

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
  {P₂ : RootPairing ι₂ R M₂ N₂} [P₂.IsCrystallographic] (b₂ : P₂.Base)
  (e : b.support ≃ b₂.support)

lemma apply_mem_range_root_of_cartanMatrixEq
    (f : M ≃ₗ[R] M₂) (hf : ∀ i : b.support, f (P.root i) = P₂.root (e i))
    (m : M) (hm : m ∈ range P.root)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    f m ∈ range P₂.root := by
  have (k : b.support) : (P.reflection k).trans f = f.trans (P₂.reflection (e k)) := by
    suffices ∀ j : b.support,
        (P.reflection k).trans f (P.root j) = f.trans (P₂.reflection (e k)) (P.root j) by
      rw [← LinearEquiv.toLinearMap_inj]
      exact b.toWeightBasis.ext fun j ↦ by simpa using this j
    intro j
    suffices P₂.pairing (e j) (e k) = P.pairing j k by simp [reflection_apply, hf, this]
    simpa only [cartanMatrixIn_def, algebraMap_pairingIn] using congr_arg (algebraMap ℤ R) (he j k)
  obtain ⟨i, rfl⟩ := hm
  apply b.induction_reflect i
  · exact fun j ⟨k, hk⟩ ↦ ⟨P₂.reflectionPerm k k, by simpa⟩
  · exact fun j hj ↦ ⟨e ⟨j, hj⟩, (hf _).symm⟩
  · intro j k ⟨l, hl⟩ hk
    replace this : f (P.reflection k (P.root j)) = (P₂.reflection (e ⟨k, hk⟩)) (f (P.root j)) := by
      simpa using LinearEquiv.congr_fun (this ⟨k, hk⟩) (P.root j)
    rw [root_reflectionPerm, this, ← hl, ← root_reflectionPerm]
    exact mem_range_self _

/-- A root system is determined by its Cartan matrix. -/
def equivOfCartanMatrixEq [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced]
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    P.Equiv P₂ :=
  let f : M ≃ₗ[R] M₂ := b.toWeightBasis.equiv b₂.toWeightBasis e
  have hf : ∀ m, f m ∈ range P₂.root ↔ m ∈ range P.root := by
    refine fun m ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa using apply_mem_range_root_of_cartanMatrixEq _ b e.symm f.symm
        (by simp [f, Module.Basis.equiv]) (f m) h (by simp [(he _ _).symm])
    · exact apply_mem_range_root_of_cartanMatrixEq b b₂ e f (by simp [f, Module.Basis.equiv]) m h he
  let : Fintype ι := Fintype.ofFinite _
  let : Fintype ι₂ := Fintype.ofFinite _
  have : DecidableEq M := Classical.typeDecidableEq M
  have : DecidableEq M₂ := Classical.typeDecidableEq M₂
  let e' : ι ≃ ι₂ := P.root.toEquivRange.trans <| (f.bijOn hf).equiv.trans P₂.root.toEquivRange.symm
  have he' (i : ι) : f (P.root i) = P₂.root (e' i) := by
    simp [f, e', BijOn.equiv, Embedding.toEquivRange]
  have : Module.IsReflexive R M₂ := .of_isPerfPair P₂.toLinearMap
  Equiv.mk' P P₂ (b.toWeightBasis.equiv b₂.toWeightBasis e) e' he'

end Uniqueness

section CartanMatrixEigenvalueFour

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℚ) (d x : ι → ℚ)
    (hH_nonneg : ∀ i j, 0 ≤ H i j) (hd_nonneg : ∀ i, 0 ≤ d i)

include hH_nonneg hd_nonneg in
private lemma abs_quadratic_le_twisted :
    (|x ·|) ⬝ᵥ (((2 - H) * diagonal d) *ᵥ (|x ·|))
      ≤ x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) := by
  simp_rw [dot_mulVec_eq_sum_sum, mul_diagonal]
  refine Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦ ?_))
  rw [mul_comm, mul_comm _ (x j), ← mul_assoc, ← mul_assoc (x j), sub_apply, add_apply,
    sub_eq_add_neg]
  by_cases hij : i = j
  · rw [← hij, abs_mul_abs_self]
    gcongr
    · exact mul_self_nonneg (x i)
    · exact hd_nonneg i
    exact neg_le_self_iff.2 (hH_nonneg i i)
  · have hbase : -(|x i| * |x j|) ≤ x i * x j :=
      neg_le_of_abs_le (le_of_eq (abs_mul ..))
    have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg (hH_nonneg i j) (hd_nonneg j))
    simp only [mul_neg, ofNat_apply, hij, ↓reduceIte, CharP.cast_eq_zero, zero_add,
      neg_mul, ge_iff_le] at hmul ⊢
    convert hmul using 1 <;> ac_rfl

include hH_nonneg hd_nonneg in
private lemma det_two_add_ne_zero_of_posDef_two_sub (hpos : ∀ x : ι → ℚ, x ≠ 0 →
  0 < x ⬝ᵥ (((2 - H) * diagonal d) *ᵥ x)) :
    ((2 + H) * diagonal d).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx_ne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let y : ι → ℚ := abs ∘ x
  have hpos_y : 0 < y ⬝ᵥ (((2 - H) * diagonal d) *ᵥ y) := by
    refine hpos y ?_
    rwa [← Function.support_nonempty_iff, Function.support_comp_eq _ abs_eq_zero,
      Function.support_nonempty_iff]
  have hle : y ⬝ᵥ (((2 - H) * diagonal d) *ᵥ y) ≤
    x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) :=
      abs_quadratic_le_twisted H d x hH_nonneg hd_nonneg
  have hx_dot : x ⬝ᵥ (((2 + H) * diagonal d) *ᵥ x) = 0 := by simp [hx]
  linarith

variable {R M N : Type*} [Field R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private lemma cartanMatrix_mul_rootLength_dot_pos {P : RootPairing ι R M N}
  [P.IsCrystallographic] (b : P.Base) [Module ℚ M] [IsScalarTower ℚ R M]
  [Module ℚ N] [IsScalarTower ℚ R N] :
  ∀ x : b.support → ℚ, x ≠ 0 →
    0 < x ⬝ᵥ (((b.cartanMatrix.map (algebraMap ℤ ℚ)) *
    diagonal (fun i : b.support ↦ (P.posRootForm ℚ).rootLength i)) *ᵥ x) := by
  intro x hx
  let B := P.posRootForm ℚ
  let v : b.support → P.rootSpan ℚ := fun i ↦ P.rootSpanMem ℚ i
  set y : P.rootSpan ℚ := ∑ i, x i • v i with y_def
  have hliQ : LinearIndependent ℚ v :=
    LinearIndependent.of_comp (P.rootSpan ℚ).subtype <|
      b.linearIndepOn_root.linearIndependent.restrict_scalars' ℚ
  have hy_ne : y ≠ 0 := by
    contrapose hx
    exact funext fun i ↦ Fintype.linearIndependent_iff.mp hliQ x (hx ▸ y_def) i
  have hpos : 0 < B.posForm y y := P.posRootForm_posForm_pos_of_ne_zero ℚ hy_ne
  have htwo (i j : b.support) :
      2 * B.posForm (v i) (v j) =
        (b.cartanMatrix i j : ℚ) * B.rootLength (j : ι) := by
    apply FaithfulSMul.algebraMap_injective ℚ R
    simp only [map_mul, map_ofNat, B.algebraMap_posForm, B.algebraMap_rootLength, B, v,
      RootPairing.Base.cartanMatrixIn_def]
    convert B.toInvariantForm.two_mul_apply_root_root i j
    exact (RootPairing.pairingIn_rat P ↑i ↑j).symm ▸ (P.algebraMap_pairingIn ℚ i j)
  have hdot : x ⬝ᵥ (((b.cartanMatrix.map (algebraMap ℤ ℚ)) *
    diagonal (fun i : b.support ↦ B.rootLength i)) *ᵥ x) =
      2 * B.posForm y y := by
    simp_rw [dot_mulVec_eq_sum_sum, mul_diagonal]
    convert_to _ = ∑ i, ∑ j, x i * (2 * B.posForm (v i) (v j)) * x j
    · simp only [y_def, Finset.univ_eq_attach, map_sum, map_smul, LinearMap.coe_sum,
      LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_)
      rw [← B.isSymm_posForm.1 (v j) (v i), RingHom.id_apply]; ac_rfl
    simp_rw [htwo, algebraMap_int_eq, Int.coe_castRingHom, map_apply]
  rwa [hdot, Rat.mul_pos_iff_of_pos_left rfl]

lemma cartanMatrix_det_four_sub_ne_zero
    {ι : Type*} [Finite ι] [DecidableEq ι] {P : RootPairing ι R M N} [P.IsCrystallographic]
    [P.IsRootSystem] (b : P.Base) :
    (4 - b.cartanMatrix).det ≠ 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _ : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  set A := b.cartanMatrix.map (algebraMap ℤ ℚ) with A_def
  set H := 2 - A with H_def
  let d : b.support → ℚ := fun i ↦ (P.posRootForm ℚ).rootLength i
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i ↦ le_of_lt ((P.posRootForm ℚ).rootLength_pos i)
  have hH_nonneg : ∀ i j, 0 ≤ H i j := by
    intro i j
    by_cases hij : i = j
    · simp [hij, H_def, A_def, Matrix.ofNat_apply]
    · simp [H_def, Matrix.ofNat_apply, hij, b.cartanMatrix_le_zero_of_ne i j hij, A_def]
  have hCD : ((2 + H) * diagonal d).det ≠ 0 := by
    refine det_two_add_ne_zero_of_posDef_two_sub H d hH_nonneg hd_nonneg (fun x hx ↦ ?_)
    convert cartanMatrix_mul_rootLength_dot_pos b x hx
    rw [H_def, sub_sub_cancel]
  contrapose hCD
  have hmap : 4 - A = (algebraMap ℤ ℚ).mapMatrix (4 - b.cartanMatrix) := by
    ext i j
    simp only [A_def, algebraMap_int_eq, Int.coe_castRingHom, sub_apply, map_apply,
      RingHom.mapMatrix_apply, Int.cast_sub, sub_left_inj, Matrix.ofNat_apply]
    split_ifs <;> rfl
  rw [H_def, ← add_sub_assoc, two_add_two_eq_four, hmap, Matrix.det_mul, ← RingHom.map_det, hCD,
    map_zero, zero_mul]

end CartanMatrixEigenvalueFour

end IsCrystallographic

end RootPairing.Base
