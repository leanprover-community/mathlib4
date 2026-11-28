/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

import Mathlib.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

This file gives the map `Matrix.toLinearEquiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

* `Matrix.toLinearEquiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

* `Matrix.exists_mulVec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear equivalence, linear isomorphism, determinant, inverse
-/

@[expose] public section

open Module

variable {m n R : Type*}

namespace Matrix

theorem SeparatingLeft.card_le [Fintype m] [Fintype n] [Ring R] [StrongRankCondition R]
    {N : Matrix m n R} (hN : N.SeparatingLeft) : Fintype.card m ≤ Fintype.card n :=
  card_le_of_injective R (vecMulLinear N) hN.vecMul_injective

theorem SeparatingRight.card_le [Fintype m] [Fintype n] [Ring R] [StrongRankCondition Rᵐᵒᵖ]
    {N : Matrix m n R} (hN : N.SeparatingRight) : Fintype.card n ≤ Fintype.card m :=
  SeparatingLeft.card_le ((separatingLeft_map_op_iff (M := Nᵀ)).mpr (by simpa using hN))

/-- Nondegenerate matrices are square. -/
theorem Nondegenerate.nonempty_equiv [Finite m] [Finite n] [Ring R]
    [StrongRankCondition R] [StrongRankCondition Rᵐᵒᵖ]
    {N : Matrix m n R} (hN : N.Nondegenerate) : Nonempty (m ≃ n) :=
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  ⟨Fintype.equivOfCardEq (le_antisymm
    (SeparatingLeft.card_le hN.separatingLeft) (SeparatingRight.card_le hN.separatingRight))⟩

variable [Fintype n]

section LinearEquiv

open LinearMap

variable {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section ToLinearEquiv'

variable [DecidableEq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `Matrix.toLinearEquiv` for the same map on arbitrary modules.
-/
def toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  GeneralLinearGroup.generalLinearEquiv _ _ <|
    Matrix.GeneralLinearGroup.toLin <| unitOfInvertible P

@[simp]
theorem toLinearEquiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (P.toLinearEquiv' h : Module.End R (n → R)) = P.mulVecLin :=
  rfl

@[simp]
theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = (⅟P).mulVecLin :=
  rfl

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

/-- Given `hA : IsUnit A.det` and `b : Basis R b`, `A.toLinearEquiv b hA` is
the `LinearEquiv` arising from `toLin b b A`.

See `Matrix.toLinearEquiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    M ≃ₗ[R] M where
  __ := toLin b b A
  toFun := toLin b b A
  invFun := toLin b b A⁻¹
  left_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA,
      toLin_one, LinearMap.id_apply]
  right_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]

theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.ker (toLin b b A) = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).injective

theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.range (toLin b b A) = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).surjective

end ToLinearEquiv

section Nondegenerate

open Matrix

/-- This holds for all integral domains (see `Matrix.exists_mulVec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
private theorem exists_mulVec_eq_zero_iff_aux {K : Type*} [DecidableEq n] [Field K]
    {M : Matrix n n K} : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective M.mulVecLin := by
      simpa only [← LinearMap.ker_eq_bot, ker_mulVecLin_eq_bot_iff, not_imp_not] using h
    have : M * (LinearEquiv.ofInjectiveEndo M.mulVecLin this).symm.toMatrix' = 1 := by
      rw [← toMatrix'_one, ← LinearEquiv.ofInjectiveEndo_right_inv, toMatrix'_mul,
        toMatrix'_mulVecLin]
    exact Matrix.det_ne_zero_of_right_inverse this

private theorem exists_mulVec_eq_zero_iff' {A : Type*} (K : Type*) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  have : (∃ v ≠ 0, (algebraMap A K).mapMatrix M *ᵥ v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine Iff.trans ?_ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => ?_) hv, ?_⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp congr($h i)
    · ext i
      refine (RingHom.map_mulVec _ _ _ i).symm.trans ?_
      rw [mul_eq, Pi.zero_apply, map_zero, Pi.zero_apply]
  · let := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => ?_) hv, ?_⟩
    · have := congr(algebraMap A K ($h i))
      rw [hf, Subtype.coe_mk, Pi.zero_apply, map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine IsFractionRing.injective A K ?_
      calc
        algebraMap A K ((M *ᵥ (fun i : n => f (v i) _)) i) =
            ((algebraMap A K).mapMatrix M *ᵥ algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]

section IsDomain
variable {A : Type*} [CommRing A] [IsDomain A] {M N : Matrix n n A}

theorem exists_mulVec_eq_zero_iff [DecidableEq n] : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0 :=
  exists_mulVec_eq_zero_iff' (FractionRing A)

theorem exists_vecMul_eq_zero_iff [DecidableEq n] : (∃ v ≠ 0, v ᵥ* M = 0) ↔ M.det = 0 := by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff

theorem nondegenerate_iff_det_ne_zero [DecidableEq n] : Nondegenerate M ↔ M.det ≠ 0 := by
  grind [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero, exists_mulVec_eq_zero_iff,
    exists_vecMul_eq_zero_iff]

alias ⟨Nondegenerate.det_ne_zero, _⟩ := nondegenerate_iff_det_ne_zero

lemma separatingLeft_iff_det_ne_zero [DecidableEq n] : SeparatingLeft M ↔ M.det ≠ 0 := by
  grind [separatingLeft_iff_forall_vecMul_eq_zero, exists_vecMul_eq_zero_iff]

lemma separatingRight_iff_det_ne_zero [DecidableEq n] : SeparatingRight M ↔ M.det ≠ 0 := by
  grind [separatingRight_iff_forall_mulVec_eq_zero, exists_mulVec_eq_zero_iff]

end IsDomain

omit [Fintype n] in
theorem separatingLeft_iff_separatingRight [Finite n] {M : Matrix n n R} :
    M.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite n
  rw [separatingLeft_iff_vecMul_injective, separatingRight_iff_mulVec_injective,
    vecMul_injective_iff, mulVec_injective_iff, ← linearIndependent_col_iff_row]

alias ⟨SeparatingLeft.separatingRight, SeparatingRight.separatingLeft⟩ :=
  separatingLeft_iff_separatingRight

omit [Fintype n] in
theorem nondegenerate_iff_separatingLeft [Finite n] {M : Matrix n n R} :
    M.Nondegenerate ↔ M.SeparatingLeft := by
  rw [nondegenerate_iff, ← separatingLeft_iff_separatingRight, and_self]

alias ⟨_, SeparatingLeft.nondegenerate⟩ := nondegenerate_iff_separatingLeft

omit [Fintype n] in
theorem nondegenerate_iff_separatingRight [Finite n] {M : Matrix n n R} :
    M.Nondegenerate ↔ M.SeparatingRight := by
  rw [nondegenerate_iff, separatingLeft_iff_separatingRight, and_self]

alias ⟨_, SeparatingRight.nondegenerate⟩ := nondegenerate_iff_separatingRight

theorem nondegenerate_iff_nonsingular [DecidableEq n] {M : Matrix n n R} :
    M.Nondegenerate ↔ M.Nonsingular := by
  rw [nondegenerate_iff, separatingLeft_iff_vecMul_injective,
    separatingRight_iff_mulVec_injective, vecMul_injective_iff, mulVec_injective_iff,
    linearIndependent_row_iff, linearIndependent_col_iff, and_self]

alias ⟨Nondegenerate.nonsingular, Nonsingular.nondegenerate⟩ := nondegenerate_iff_nonsingular

omit [Fintype n] in
theorem Nondegenerate.mul_iff_right {l m : Type*} [Finite l] [Fintype m] [Finite n]
    {M : Matrix l m R} {N : Matrix m n R} (h : N.Nondegenerate) :
    (M * N).Nondegenerate ↔ M.Nondegenerate := by
  by_cases! Subsingleton R
  · simp [nondegenerate_iff, SeparatingLeft, SeparatingRight, Subsingleton.eq_zero]
  obtain ⟨e₂⟩ := h.nonempty_equiv
  by_cases hlm : Nonempty (l ≃ m)
  · obtain ⟨e₁⟩ := hlm
    classical
    rw [← nondegenerate_submatrix_iff e₁.symm.bijective e₂.bijective (M := M * N),
      ← nondegenerate_submatrix_iff e₁.symm.bijective Function.bijective_id (M := M)]
    simp [submatrix_mul (e₂ := id), nondegenerate_iff_nonsingular, nonsingular_mul_iff,
      (h.submatrix _ e₂.bijective).nonsingular]
  · refine iff_of_false (fun hMN ↦ hlm ?_) (fun hM ↦ hlm hM.nonempty_equiv)
    obtain ⟨e₁⟩ := hMN.nonempty_equiv
    exact ⟨e₁.trans e₂.symm⟩

omit [Fintype n] in
theorem Nondegenerate.mul_iff_left {l m : Type*} [Finite l] [Fintype m] [Finite n]
    {M : Matrix l m R} {N : Matrix m n R} (h : M.Nondegenerate) :
    (M * N).Nondegenerate ↔ N.Nondegenerate := by
  rw [← nondegenerate_transpose_iff (M := M * N), transpose_mul,
    Nondegenerate.mul_iff_right h.transpose, nondegenerate_transpose_iff]

omit [Fintype n] in
@[deprecated nondegenerate_smul_iff +typeChanged (since := "2026-11-24")]
theorem Nondegenerate.smul_iff
    {A : Type*} [CommRing A] [IsDomain A] [Finite n] {t : A} (h : t ≠ 0)
    {M : Matrix n n A} :
    (t • M).Nondegenerate ↔ M.Nondegenerate :=
  nondegenerate_smul_iff <| .of_ne_zero h

end Nondegenerate

end LinearEquiv

section Determinant

/-- A matrix whose nondiagonal entries are negative with the sum of the entries of each
column positive has nonzero determinant. -/
lemma det_ne_zero_of_sum_col_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : ∀ j, 0 < ∑ i, A i j) :
    A.det ≠ 0 := by
  cases isEmpty_or_nonempty n
  · simp
  · contrapose! h2
    obtain ⟨v, ⟨h_vnz, h_vA⟩⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h2
    wlog h_sup : 0 < Finset.sup' Finset.univ Finset.univ_nonempty v
    · refine this h1 inferInstance h2 (-1 • v) (by simp [*]) ?_ ?_
      · rw [Matrix.smul_vecMul, h_vA, smul_zero]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h_vnz
        simp_rw [Finset.lt_sup'_iff, Finset.mem_univ, true_and] at h_sup ⊢
        simp_rw [not_exists, not_lt] at h_sup
        refine ⟨i, ?_⟩
        rw [Pi.smul_apply, neg_smul, one_smul, Left.neg_pos_iff]
        exact Ne.lt_of_le hi (h_sup i)
    · obtain ⟨j₀, -, h_j₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
      refine ⟨j₀, ?_⟩
      rw [← mul_le_mul_iff_right₀ (h_j₀ ▸ h_sup), Finset.mul_sum, mul_zero]
      rw [show 0 = ∑ i, v i * A i j₀ from congr($h_vA j₀).symm]
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h : i = j₀
      · rw [h]
      · exact (mul_le_mul_right_of_neg (h1 h)).mpr (h_j₀ ▸ Finset.le_sup' v hi)

/-- A matrix whose nondiagonal entries are negative with the sum of the entries of each
row positive has nonzero determinant. -/
lemma det_ne_zero_of_sum_row_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : ∀ i, 0 < ∑ j, A i j) :
    A.det ≠ 0 := by
  rw [← Matrix.det_transpose]
  refine det_ne_zero_of_sum_col_pos ?_ ?_
  · simp_rw [Matrix.transpose_apply]
    exact fun i j h => h1 h.symm
  · simp_rw [Matrix.transpose_apply]
    exact h2

end Determinant

end Matrix
