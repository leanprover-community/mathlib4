/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix
* `Matrix.cRank`: the rank of a matrix as a cardinal
* `Matrix.eRank`: the rank of a matrix as a term in `ℕ∞`.

## Main results

* `Matrix.rank_eq_finrank_range_toLin`: the rank equals the dimension of the range of the
corresponding linear map, and is therefore independent of the choice of bases.
* `Matrix.rank_eq_finrank_span_cols`, `Matrix.rank_eq_finrank_span_row`: the rank equals the
dimension of the space spanned by the columns (resp. rows).
* `Matrix.rank_transpose`: transposing a matrix does not change its rank.
* `Matrix.rank_mul_le`: the rank of `A * B` is at most the rank of `A` and at most the rank of `B`.
* `Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det`: multiplying by
an invertible matrix does not change the rank.
* `Matrix.exists_rank_normal_form`: every square matrix over a field can be brought, by left and
right multiplication by invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the
identity block has size equal to the rank of the matrix.
* `Matrix.rank_add_le`: the rank of `A + B` is at most the rank of `A` plus the rank of `B`.
* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity for matrices.
* `Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁`: the rank of a block upper triangular matrix is
at least the sum of the ranks of its diagonal blocks.
-/

@[expose] public section

open Matrix

namespace Matrix

open Module Cardinal Set Submodule

universe ul um um₀ un un₀ uo uR
variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}
variable {R : Type uR}

section Infinite

variable [Semiring R]

/-- The rank of a matrix, defined as the dimension of its column space, as a cardinal. -/
noncomputable def cRank (A : Matrix m n R) : Cardinal := Module.rank R <| span R <| range A.col

@[simp]
theorem cRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.cRank = 1 :=
  rank_subsingleton _ _

lemma cRank_toNat_eq_finrank (A : Matrix m n R) :
    A.cRank.toNat = Module.finrank R (span R (range A.col)) := rfl

lemma lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    lift.{um} (A.submatrix r c).cRank ≤ lift.{um₀} A.cRank := by
  have h : ((A.submatrix r id).submatrix id c).cRank ≤ (A.submatrix r id).cRank :=
    Submodule.rank_mono <| span_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m → R) →ₗ[R] (m₀ → R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (range A.col)) = span R (range (A.submatrix r id).col) := by
    simp_rw [LinearMap.map_span, ← image_univ, image_image, col_eq_transpose, transpose_submatrix]
    aesop
  rw [cRank, ← h_eq]
  have hwin := lift_rank_map_le f (span R (range Aᵀ))
  simp_rw [← lift_umax] at hwin ⊢
  exact hwin

/-- A special case of `lift_cRank_submatrix_le` for when `m₀` and `m` are in the same universe. -/
lemma cRank_submatrix_le {m m₀ : Type um} (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).cRank ≤ A.cRank := by
  simpa using lift_cRank_submatrix_le A r c

lemma cRank_le_card_height [StrongRankCondition R] [Fintype m] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card m :=
  (Submodule.rank_le (span R (range Aᵀ))).trans <| by rw [rank_fun']

lemma cRank_le_card_width [StrongRankCondition R] [Fintype n] (A : Matrix m n R) :
    A.cRank ≤ Fintype.card n :=
  (rank_span_le ..).trans <|
    by simpa [col_eq_transpose] using Cardinal.mk_range_le_lift (f := A.col)

/-- The rank of a matrix, defined as the dimension of its column space, as a term in `ℕ∞`. -/
noncomputable def eRank (A : Matrix m n R) : ℕ∞ := A.cRank.toENat

@[simp]
theorem eRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.eRank = 1 := by
  simp [eRank]

lemma eRank_toNat_eq_finrank (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range A.col)) :=
  toNat_toENat ..

lemma eRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).eRank ≤ A.eRank := by
  simpa using! OrderHom.mono (β := ℕ∞) Cardinal.toENat <| lift_cRank_submatrix_le A r c

lemma eRank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card n := by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_natCast]
  exact A.cRank_le_card_width

lemma eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card m := by
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_natCast]
  exact A.cRank_le_card_height

end Infinite

variable [Fintype n] [Fintype o]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank [CommSemiring R] (A : Matrix m n R) : ℕ :=
  finrank R <| LinearMap.range A.mulVecLin

@[simp]
theorem rank_subsingleton [CommSemiring R] [Subsingleton R] (A : Matrix m n R) : A.rank = 1 :=
  finrank_subsingleton

@[simp]
theorem cRank_one [Semiring R] [DecidableEq m] [StrongRankCondition R] :
    (cRank (1 : Matrix m m R)) = lift.{uR} #m := by
  have h : LinearIndependent R (1 : Matrix m m R).col := by
    convert! Pi.linearIndependent_single_one m R
    simp [funext_iff, one_apply, Pi.single_apply]
  rw [cRank, rank_span h, ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']

@[simp] theorem eRank_one [Semiring R] [DecidableEq m] [StrongRankCondition R] :
    (eRank (1 : Matrix m m R)) = ENat.card m := by
  rw [eRank, cRank_one, toENat_lift, ENat.card]

@[simp]
theorem rank_one [CommSemiring R] [DecidableEq n] [StrongRankCondition R] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, mulVecLin_one, LinearMap.range_id, finrank_top, finrank_pi]

@[simp]
theorem rank_zero [CommSemiring R] [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, mulVecLin_zero, LinearMap.range_zero, finrank_bot]

@[simp]
theorem cRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : cRank (0 : Matrix m n R) = 0 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank, col_eq_transpose, transpose_zero, of_symm_zero, range_zero, span_zero_singleton,
    rank_bot]

@[simp]
theorem eRank_zero {m n : Type*} [Semiring R] [Nontrivial R] : eRank (0 : Matrix m n R) = 0 := by
  simp [eRank]

theorem rank_le_card_width [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card n :=
  A.mulVecLin.finrank_range_le.trans_eq <| finrank_pi R

theorem rank_le_width [CommSemiring R] [StrongRankCondition R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : A.rank ≤ n :=
  A.rank_le_card_width.trans (Fintype.card_fin n).le

theorem rank_mul_le_left [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank ≤ A.rank := by
  nontriviality R
  rw [rank, rank, mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left ..) (rank_lt_aleph0 R _)

theorem rank_mul_le_right [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (B : Matrix n o R) : (A * B).rank ≤ B.rank := by
  nontriviality R
  rw [rank, rank, mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)

theorem rank_mul_le [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

theorem rank_mul_ge [CommRing R] [IsDomain R] (A : Matrix m n R) (B : Matrix n o R) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  have hker : finrank R (A.mulVecLin.comp B.mulVecLin).ker ≤
      finrank R A.mulVecLin.ker + finrank R B.mulVecLin.ker := by
    have H := B.mulVecLin.lift_rank_comap_le A.mulVecLin.ker
    simp only [← Submodule.finrank_eq_rank, Cardinal.lift_natCast] at H
    exact_mod_cast H
  have hf := A.mulVecLin.finrank_range_add_finrank_ker
  have hg := B.mulVecLin.finrank_range_add_finrank_ker
  have hfg := (A.mulVecLin.comp B.mulVecLin).finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card] at hf hg hfg
  rw [rank, rank, rank, mulVecLin_mul]
  lia

theorem rank_vecMulVec_le [CommSemiring R] [StrongRankCondition R] (w : m → R) (v : n → R) :
    (Matrix.vecMulVec w v).rank ≤ 1 := by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (rank_mul_le_left _ _) ?_
  nontriviality R
  exact rank_le_card_width _

theorem rank_unit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this

theorem rank_of_isUnit [DecidableEq n] [CommSemiring R] [StrongRankCondition R] (A : Matrix n n R)
    (h : IsUnit A) : A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A

theorem rank_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [Nontrivial R]
    [Fintype m] [DecidableEq m] {A : Matrix m m R} (hA : A.det ∈ nonZeroDivisors R) :
    A.rank = Fintype.card m := by
  rw [rank, LinearMap.finrank_range_of_inj (mulVec_injective_of_det_mem_nonZeroDivisors hA),
    Module.finrank_eq_card_basis (Pi.basisFun R m)]

theorem rank_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [DecidableEq m]
    {A : Matrix m m R} (h : A.det ≠ 0) : A.rank = Fintype.card m :=
  rank_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)

lemma rank_smul_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {c : R} (B : Matrix m n R)
    (hc : c ∈ nonZeroDivisors R) : (c • B).rank = B.rank := by
  have hc' : IsSMulRegular R c := isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr hc.1
  have hreg : IsSMulRegular (m → R) c := IsSMulRegular.pi fun _ => hc'
  let f := LinearMap.lsmul R (m → R) c
  have hcomp : (c • B).mulVecLin = f.comp B.mulVecLin := by aesop
  rw [rank, rank, hcomp, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective f hreg _).finrank_eq.symm

lemma rank_mul_eq_left_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : A.det ∈ nonZeroDivisors R) :
    (B * A).rank = B.rank := by
  nontriviality R
  refine le_antisymm (rank_mul_le_left B A) ?_
  have key : (B * A) * A.adjugate = A.det • B := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  calc B.rank = (A.det • B).rank := (rank_smul_of_mem_nonZeroDivisors B hA).symm
    _ = ((B * A) * A.adjugate).rank := by rw [key]
    _ ≤ (B * A).rank := rank_mul_le_left _ _

lemma rank_mul_eq_left_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (h : A.det ≠ 0) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Right multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_left_of_isUnit_det {R : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n R)
    (B : Matrix m n R) (hA : IsUnit A.det) : (B * A).rank = B.rank :=
  rank_mul_eq_left_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

lemma rank_mul_eq_right_of_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.det ∈ nonZeroDivisors R) : (A * B).rank = B.rank := by
  rw [rank, rank, mulVecLin_mul, LinearMap.range_comp,
    ← (Submodule.equivMapOfInjective A.mulVecLin
      (mulVec_injective_of_det_mem_nonZeroDivisors hA) _).finrank_eq]

lemma rank_mul_eq_right_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Matrix m n R) (h : A.det ≠ 0) :
    (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B (mem_nonZeroDivisors_of_ne_zero h)

/-- Left multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_right_of_isUnit_det {R : Type*} [CommRing R] [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) : (A * B).rank = B.rank :=
  rank_mul_eq_right_of_det_mem_nonZeroDivisors A B hA.mem_nonZeroDivisors

lemma rank_mul_eq_right_of_isLowerTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsLowerTriangular) (hd : ∀ i, A.diag i ≠ 0) : (A * B).rank = B.rank := by
  have hdet : A.det ≠ 0 := by simpa [det_of_isLowerTriangular A hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

lemma rank_mul_eq_right_of_isUpperTriangular {R : Type*} [CommRing R] [IsDomain R]
    [Fintype m] [LinearOrder m] (A : Matrix m m R) (B : Matrix m n R)
    (hA : A.IsUpperTriangular) (hd : ∀ i, A.diag i ≠ 0) : (A * B).rank = B.rank := by
  have hdet : A.det ≠ 0 := by simpa [det_of_isUpperTriangular hA, Finset.prod_ne_zero_iff]
  exact rank_mul_eq_right_of_det_ne_zero A B hdet

/-- Taking a subset of the rows and columns reduces the rank. -/
theorem rank_submatrix_le [CommSemiring R] [StrongRankCondition R] [Fintype n₀] (A : Matrix m n R)
    (r : m₀ → m) (c : n₀ → n) : (A.submatrix r c).rank ≤ A.rank := by
  nontriviality R
  have := Module.Finite.span_of_finite R (Set.finite_range (A.submatrix r id).col)
  calc
    _ = (((A.submatrix r id)ᵀᵀ.submatrix id c)ᵀᵀ).rank := by simp
    _ ≤ finrank R (span R (range (A.submatrix r id).col)) := by
      rw [rank, Matrix.mulVecLin_transpose, Matrix.transpose_submatrix, transpose_transpose,
        range_vecMulLinear, ← Matrix.transpose_submatrix, row_transpose]
      exact Submodule.finrank_mono (Submodule.span_mono (fun v ⟨j, hj⟩ => ⟨c j, hj⟩))
    _ = (A.submatrix r id)ᵀᵀ.rank := by
      rw [rank, Matrix.mulVecLin_transpose, range_vecMulLinear]
      rfl
    _ = (A.submatrix r (Equiv.refl n)).rank := by simp
  rw [rank, rank, mulVecLin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R (Equiv.refl n).symm = LinearEquiv.funCongrLeft R R
      (Equiv.refl n).symm from rfl, LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _

theorem rank_reindex [Fintype n₀] [CommSemiring R] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) :
    rank (A.reindex em en) = rank A := by
  rw [rank, rank, mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

@[simp]
theorem rank_submatrix [Fintype n₀] [CommSemiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : rank (A.submatrix em en) = rank A := by
  simpa only [reindex_apply] using! rank_reindex em.symm en.symm A

@[simp]
theorem lift_cRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : lift.{um} (cRank (A.submatrix em en)) = lift.{um₀} (cRank A) :=
  (A.lift_cRank_submatrix_le em en).antisymm
    <| by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

/-- A special case of `lift_cRank_submatrix` for when the row types are in the same universe. -/
@[simp]
theorem cRank_submatrix {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : cRank (A.submatrix em en) = cRank A := by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en

theorem lift_cRank_reindex {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : lift.{um} (cRank (A.reindex em en)) = lift.{um₀} (cRank A) :=
  lift_cRank_submatrix ..

/-- A special case of `lift_cRank_reindex` for when the row types are in the same universe. -/
theorem cRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : cRank (A.reindex em en) = cRank A :=
  cRank_submatrix ..

@[simp]
theorem eRank_submatrix {n : Type un} [Semiring R] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    eRank (A.submatrix em en) = eRank A := by
  simpa [-lift_cRank_submatrix] using! congr(Cardinal.toENat $(A.lift_cRank_submatrix em en))

theorem eRank_reindex {m₀ : Type um} {n : Type un} [Semiring R] (A : Matrix m n R) (em : m ≃ m₀)
    (en : n ≃ n₀) : eRank (A.reindex em en) = eRank A :=
  eRank_submatrix ..

/-- The rank of a matrix equals the dimension of the range of the corresponding linear map,
and is therefore independent of the choice of bases. -/
theorem rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R)
    (v₁ : Basis m R M₁) (v₂ : Basis n R M₂) :
    A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) e₂.range]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin', toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply] at aux₁ aux₂
  simp only [e₁, e₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply,
    aux₁, aux₂, LinearMap.coe_single, toLin_self, map_sum, map_smul, Basis.equiv_apply]

theorem rank_le_card_height [Fintype m] [CommSemiring R] [StrongRankCondition R]
    (A : Matrix m n R) : A.rank ≤ Fintype.card m :=
  (Submodule.finrank_le _).trans (finrank_pi R).le

/-- The rank of a matrix is at most the size of any finset containing all its nonzero rows. -/
theorem rank_le_card_of_support_subset [CommSemiring R] [StrongRankCondition R] (A : Matrix m n R)
    (s : Finset m) (hz : Function.support A.row ⊆ s) : A.rank ≤ s.card := by
  rw [Function.support_subset_iff'] at hz
  classical
  set B : Matrix m {x // x ∈ s} R := Matrix.of fun i a => if (a : m) = i then 1 else 0 with hBdef
  have hB : B * A.submatrix Subtype.val id = A := by
    ext i j
    simp only [hBdef, mul_apply, of_apply, submatrix_apply, id_eq]
    by_cases hi : i ∈ s
    · rw [Fintype.sum_eq_single (⟨i, hi⟩ : {x // x ∈ s})
        fun a ha => by rw [ite_eq_right fun he => ha (Subtype.ext he), zero_mul],
        ite_eq_left rfl, one_mul]
    · have h0 : A i = 0 := hz i hi
      aesop
  calc A.rank = (B * A.submatrix Subtype.val id).rank := by rw [hB]
    _ ≤ (A.submatrix Subtype.val id).rank := rank_mul_le_right _ _
    _ ≤ Fintype.card {x // x ∈ s} := rank_le_card_height _
    _ = s.card := Fintype.card_coe s

theorem rank_le_height [CommSemiring R] [StrongRankCondition R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : A.rank ≤ m :=
  A.rank_le_card_height.trans (Fintype.card_fin m).le

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
theorem rank_eq_finrank_span_cols [CommSemiring R] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.col)) := by rw [rank, Matrix.range_mulVecLin]

@[simp]
theorem cRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.cRank.toNat = A.rank := by
  rw [cRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

@[simp]
theorem eRank_toNat_eq_rank [CommSemiring R] (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

section Field

variable [Field R]

/-- The rank of a diagonal matrix is the count of non-zero elements on its main diagonal -/
theorem rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m → R) :
    (diagonal w).rank = Fintype.card {i // (w i) ≠ 0} := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', Module.finrank, ← LinearMap.rank,
    LinearMap.rank_diagonal, Cardinal.toNat_natCast]

open TransvectionStruct in
/-- Every square matrix over a field can be brought, by left and right multiplication by
invertible matrices, into the block form `fromBlocks 1 0 0 0`, where the identity block has size
equal to the rank of the matrix. -/
theorem exists_rank_normal_form [Fintype m] [DecidableEq m] (M : Matrix m m R) :
    ∃ (V U : Matrix m m R) (e : m ≃ Fin M.rank ⊕ Fin (Fintype.card m - M.rank)),
      IsUnit V ∧ IsUnit U ∧
      V * M * U = (fromBlocks 1 0 0 0).submatrix e e := by
  classical
  obtain ⟨L, L', D, hM0⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set E := fun i ↦ if D i = 0 then 1 else (D i)⁻¹ with E_def
  set s : Finset m := .filter (fun i ↦ D i ≠ 0) .univ with s_def
  set V := diagonal E * (L.reverse.map (toMatrix ∘ .inv)).prod with V_def
  set U := (L'.reverse.map (toMatrix ∘ .inv)).prod with U_def
  have hUdet : IsUnit U.det := (isUnit_iff_isUnit_det _).1 <| isUnit_prod_comp_inverse _
  have hVdet : IsUnit V.det := by
    rw [V_def, det_mul, det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 (by grind)) |>.mul <|
      (isUnit_iff_isUnit_det _).1 (isUnit_prod_comp_inverse _)
  have hM : V * M * U = diagonal (fun i ↦ if i ∈ s then 1 else 0) := by
    rw [V_def, U_def, hM0, mul_assoc, mul_assoc _ (L'.map _).prod, prod_mul_reverse_inv_prod,
      mul_one, ← mul_assoc, mul_assoc _ (L.reverse.map _).prod, reverse_inv_prod_mul_prod, mul_one]
    ext
    simp only [E_def, mul_diagonal, diagonal_apply, ite_mul, one_mul, zero_mul, s_def,
      Finset.mem_filter, Finset.mem_univ, true_and, ite_not]
    split_ifs with h1 h2 <;> first | rw [← h1, h2] | rw [← h1, inv_mul_cancel₀ h2] | rfl
  have hs : s.card = M.rank := by
    simp [← rank_mul_eq_right_of_isUnit_det V M hVdet, ← rank_mul_eq_left_of_isUnit_det U (V * M)
      hUdet, hM, rank_diagonal]
  set e : m ≃ Fin M.rank ⊕ Fin (Fintype.card m - M.rank) :=
    (Equiv.sumCompl (· ∈ s)).symm.trans <| (Finset.equivFinOfCardEq hs).sumCongr <|
      Fintype.equivFinOfCardEq <| by rw [Fintype.card_subtype_compl, Fintype.card_coe, hs] with he
  refine ⟨V, U, e, (isUnit_iff_isUnit_det _).2 hVdet, isUnit_prod_comp_inverse _, ?_⟩
  rw [hM, ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, submatrix_diagonal_equiv]
  refine congrArg _ (funext fun i ↦ ?_)
  split_ifs with hi <;> simp [he, hi]

theorem cRank_diagonal [DecidableEq m] (w : m → R) :
    (diagonal w).cRank = lift.{uR} #{i // (w i) ≠ 0} := by
  classical
  set w' : {i // (w i) ≠ 0} → _ := fun i ↦ (diagonal w) i
  have h : LinearIndependent R w' := by
    have hli' := Pi.linearIndependent_single_of_ne_zero (R := R)
      (v := fun i : m ↦ if w i = 0 then (1 : R) else w i) (by simp [ite_eq_iff'])
    convert hli'.comp Subtype.val Subtype.val_injective
    ext ⟨j, hj⟩ k
    simp [w', diagonal, hj, Pi.single_apply, eq_comm]
  have hrw : insert 0 (range (diagonal w).col) = insert 0 (range w') := by
    suffices ∀ a, diagonal w a = 0 ∨ ∃ b, w b ≠ 0 ∧ diagonal w b = diagonal w a
      by aesop (add simp [col_eq_transpose, subset_def])
    simp_rw [or_iff_not_imp_right, not_exists, not_and, not_imp_not]
    simp +contextual [funext_iff, diagonal]
  rw [cRank, ← span_insert_zero, hrw, span_insert_zero, rank_span h,
    ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']

theorem eRank_diagonal [DecidableEq m] (w : m → R) :
    (diagonal w).eRank = {i | (w i) ≠ 0}.encard := by
  simp [eRank, cRank_diagonal, toENat_cardinalMk_subtype]

end Field

/-! ### Lemmas about transpose and conjugate transpose

This section contains lemmas about the rank of `Matrix.transpose` and `Matrix.conjTranspose`.

Unfortunately the proofs are essentially duplicated between the two; `ℚ` is a linearly-ordered ring
but can't be a star-ordered ring, while `ℂ` is star-ordered (with `open ComplexOrder`) but
not linearly ordered. For now we don't prove the transpose case for `ℂ`.

TODO: the lemmas `Matrix.rank_transpose` and `Matrix.rank_conjTranspose` current follow a short
proof that is a simple consequence of `Matrix.rank_transpose_mul_self` and
`Matrix.rank_conjTranspose_mul_self`. This proof pulls in unnecessary assumptions on `R`, and should
be replaced with a proof that uses Gaussian reduction or argues via linear combinations.
-/

section StarOrderedField

variable [Fintype m] [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem ker_mulVecLin_conjTranspose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᴴ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, conjTranspose_mul_self_mulVec_eq_zero]

theorem rank_conjTranspose_mul_self (A : Matrix m n R) : (Aᴴ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ * A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

-- this follows the proof here https://math.stackexchange.com/a/81903/1896
/-- TODO: prove this in greater generality. -/
@[simp]
theorem rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]
theorem rank_self_mul_conjTranspose (A : Matrix m n R) : (A * Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose, conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self Aᴴ

end StarOrderedField

section LinearOrderedField

variable [Fintype m] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem ker_mulVecLin_transpose_mul_self (A : Matrix m n R) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr(dotProduct x $h)
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_transpose, dotProduct_self_eq_zero] at h
  · intro h
    rw [h, mulVec_zero]

theorem rank_transpose_mul_self (A : Matrix m n R) : (Aᵀ * A).rank = A.rank := by
  dsimp only [rank]
  refine add_left_injective (finrank R <| LinearMap.ker A.mulVecLin) ?_
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᵀ * A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᵀ * A)) }
  · rw [ker_mulVecLin_transpose_mul_self]
  · simp only [LinearMap.finrank_range_add_finrank_ker]

end LinearOrderedField

@[simp]
theorem rank_transpose [Field R] [Fintype m] (A : Matrix m n R) : Aᵀ.rank = A.rank := by
  classical
  rw [Aᵀ.rank_eq_finrank_range_toLin (Pi.basisFun R n).dualBasis (Pi.basisFun R m).dualBasis,
      toLin_transpose, ← LinearMap.dualMap_def, LinearMap.finrank_range_dualMap_eq_finrank_range,
      toLin_eq_toLin', toLin'_apply', rank]

@[simp]
theorem rank_self_mul_transpose [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] (A : Matrix m n R) :
    (A * Aᵀ).rank = A.rank := by
  simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

/-- The rank of a matrix is the rank of the space spanned by its rows. -/
theorem rank_eq_finrank_span_row [Field R] [Finite m] (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.row)) := by
  cases nonempty_fintype m
  rw [← rank_transpose, rank_eq_finrank_span_cols, col_transpose]

theorem _root_.LinearIndependent.rank_matrix [Field R] [Fintype m]
    {M : Matrix m n R} (h : LinearIndependent R M.row) : M.rank = Fintype.card m := by
  rw [M.rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span.mp h, Set.finrank]

/-- `M.mulVec` is surjective iff `M` has full row rank. -/
theorem mulVec_surjective_iff_rank_eq_card [Field R] [Fintype m] {M : Matrix m n R} :
    M.mulVec.Surjective ↔ M.rank = Fintype.card m := by
  rw [← coe_mulVecLin, ← LinearMap.range_eq_top, rank, ← Module.finrank_pi R]
  exact ⟨fun h ↦ by rw [h, finrank_top], Submodule.eq_top_of_finrank_eq⟩

/-- A matrix over a semisimple ring with linearly independent rows has surjective `mulVec`. -/
theorem _root_.LinearIndependent.mulVec_surjective [Ring R] [IsSemisimpleRing R]
    {M : Matrix m n R} (h : LinearIndependent R M.row) : M.mulVec.Surjective := by
  nontriviality R using M.mulVec.surjective_to_subsingleton
  have := @Fintype.ofFinite m h.finite_of_isNoetherian
  classical
  have ⟨f, hf⟩ := IsSemisimpleModule.extension_property M.toLinearMapRight'
    (vecMul_injective_iff.mpr h) .id
  have : M * f.toMatrixRight' = 1 := toLinearMapRight'.injective <| by simpa using hf
  exact fun v ↦ ⟨f.toMatrixRight' *ᵥ v, by simp [this]⟩

/-- `M.vecMul` is surjective iff `M` has full column rank. -/
theorem vecMul_surjective_iff_rank_eq_card [Field R] [Fintype m] {M : Matrix m n R} :
    M.vecMul.Surjective ↔ M.rank = Fintype.card n := by
  simp [← mulVec_transpose, mulVec_surjective_iff_rank_eq_card]

omit [Fintype n] in
/-- A matrix with linearly independent columns has surjective `vecMul`. -/
theorem _root_.LinearIndependent.vecMul_surjective [CommRing R] [IsSemisimpleRing R]
    [Fintype m] {M : Matrix m n R} (h : LinearIndependent R M.col) : M.vecMul.Surjective := by
  simpa [← mulVec_transpose] using h.mulVec_surjective

lemma rank_add_rank_le_card_of_mul_eq_zero [Field R] [Finite l] [Fintype m]
    {A : Matrix l m R} {B : Matrix m n R} (hAB : A * B = 0) :
    A.rank + B.rank ≤ Fintype.card m := by
  classical
  let el : Basis l R (l → R) := Pi.basisFun R l
  let em : Basis m R (m → R) := Pi.basisFun R m
  let en : Basis n R (n → R) := Pi.basisFun R n
  rw [Matrix.rank_eq_finrank_range_toLin A el em,
      Matrix.rank_eq_finrank_range_toLin B em en,
      ← Module.finrank_fintype_fun_eq_card R,
      ← LinearMap.finrank_range_add_finrank_ker (Matrix.toLin em el A),
      add_le_add_iff_left]
  apply Submodule.finrank_mono
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin_mul, hAB, map_zero]

section RankAdd

variable [Field R] {p : Type*}

/-- Subadditivity of the rank of matrices. -/
theorem rank_add_le (A B : Matrix m n R) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Negating a matrix does not change its rank. -/
@[simp]
theorem rank_neg (A : Matrix m n R) : (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := LinearMap.ext fun v => neg_mulVec v A
  rw [rank, rank, h, LinearMap.range_neg]

/-- The rank of a difference is at most the sum of the ranks. -/
theorem rank_sub_le (A B : Matrix m n R) : (A - B).rank ≤ A.rank + B.rank := by
  simpa [sub_eq_add_neg] using rank_add_le A (-B)

/-- Rank–nullity for matrices: the rank plus the dimension of the kernel of `A.mulVecLin` is the
number of columns. -/
theorem rank_add_finrank_ker_mulVecLin (A : Matrix m n R) :
    A.rank + finrank R (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- If `U` is invertible, the nullity of `U + E` is at most the rank of `E`. -/
theorem finrank_ker_mulVecLin_add_le [DecidableEq n] {U : Matrix n n R} (hU : IsUnit U)
    (E : Matrix n n R) : finrank R (LinearMap.ker (U + E).mulVecLin) ≤ E.rank := by
  have h1 := rank_add_finrank_ker_mulVecLin (U + E)
  have h2 : U.rank ≤ (U + E).rank + (-E).rank := by
    simpa using rank_add_le (U + E) (-E)
  rw [rank_of_isUnit U hU, rank_neg] at h2
  omega

/-- If `U` is invertible, the nullity of `U - E` is at most the rank of `E`. -/
theorem finrank_ker_mulVecLin_sub_le [DecidableEq n] {U : Matrix n n R} (hU : IsUnit U)
    (E : Matrix n n R) : finrank R (LinearMap.ker (U - E).mulVecLin) ≤ E.rank := by
  rw [sub_eq_add_neg, ← rank_neg E]
  exact finrank_ker_mulVecLin_add_le hU (-E)

/-- If `U` is invertible and `P` has columns indexed by `o`, the nullity of `U - P * Q` is at most
`Fintype.card o`. -/
theorem finrank_ker_mulVecLin_sub_mul_le [DecidableEq n] {U : Matrix n n R}
    (hU : IsUnit U) (P : Matrix n o R) (Q : Matrix o n R) :
    finrank R (LinearMap.ker (U - P * Q).mulVecLin) ≤ Fintype.card o :=
  (finrank_ker_mulVecLin_sub_le hU _).trans <|
    (rank_mul_le_left P Q).trans (rank_le_card_width P)

/-- The nullity of a block upper triangular matrix is at most the sum of the nullities of its
diagonal blocks. -/
theorem finrank_ker_mulVecLin_fromBlocks_zero₂₁_le (A : Matrix l n R) (B : Matrix l o R)
    (D : Matrix p o R) :
    finrank R (LinearMap.ker (fromBlocks A B 0 D).mulVecLin) ≤
      finrank R (LinearMap.ker A.mulVecLin) + finrank R (LinearMap.ker D.mulVecLin) := by
  set KM := LinearMap.ker (fromBlocks A B 0 D).mulVecLin
  have hmem : ∀ v : KM, A *ᵥ ((v : n ⊕ o → R) ∘ Sum.inl) + B *ᵥ ((v : n ⊕ o → R) ∘ Sum.inr) = 0
      ∧ D *ᵥ ((v : n ⊕ o → R) ∘ Sum.inr) = 0 := by
    intro v
    have hv : fromBlocks A B 0 D *ᵥ (v : n ⊕ o → R) = 0 := v.2
    rw [fromBlocks_mulVec] at hv
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun hv (Sum.inl i)
    · simpa using congrFun hv (Sum.inr i)
  let f : KM →ₗ[R] (o → R) := (LinearMap.funLeft R R Sum.inr).comp KM.subtype
  have hf : ∀ v : KM, f v = (v : n ⊕ o → R) ∘ Sum.inr := fun v => rfl
  have hfr : LinearMap.range f ≤ LinearMap.ker D.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, hf]
    exact (hmem v).2
  let g : LinearMap.ker f →ₗ[R] (n → R) :=
    (LinearMap.funLeft R R Sum.inl).comp (KM.subtype.comp (LinearMap.ker f).subtype)
  have hg : ∀ u : LinearMap.ker f, g u = ((u : KM) : n ⊕ o → R) ∘ Sum.inl := fun u => rfl
  have hinr : ∀ u : LinearMap.ker f, ((u : KM) : n ⊕ o → R) ∘ Sum.inr = 0 := by
    intro u
    rw [← hf]
    exact u.2
  have hginj : Function.Injective g := by
    intro u u' hu
    rw [hg, hg] at hu
    apply Subtype.ext
    apply Subtype.ext
    funext s
    rcases s with i | i
    · exact congrFun hu i
    · exact (congrFun (hinr u) i).trans (congrFun (hinr u') i).symm
  have hgr : LinearMap.range g ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, hg]
    have h := (hmem (u : KM)).1
    rwa [hinr u, mulVec_zero, add_zero] at h
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank R (LinearMap.range f) ≤ finrank R (LinearMap.ker D.mulVecLin) :=
    Submodule.finrank_mono hfr
  have h3 : finrank R (LinearMap.ker f) ≤ finrank R (LinearMap.ker A.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hginj]
    exact Submodule.finrank_mono hgr
  omega

/-- The rank of a block upper triangular matrix is at least the sum of the ranks of its diagonal
blocks. -/
theorem rank_add_rank_le_rank_fromBlocks_zero₂₁ (A : Matrix l n R) (B : Matrix l o R)
    (D : Matrix p o R) : A.rank + D.rank ≤ (fromBlocks A B 0 D).rank := by
  have h := finrank_ker_mulVecLin_fromBlocks_zero₂₁_le A B D
  have hA := rank_add_finrank_ker_mulVecLin A
  have hD := rank_add_finrank_ker_mulVecLin D
  have hM := rank_add_finrank_ker_mulVecLin (fromBlocks A B 0 D)
  rw [Fintype.card_sum] at hM
  omega

/-- The rank of `fromBlocks A B 0 D` is at most the rank of `A` plus the number of columns
of `D`. -/
theorem rank_fromBlocks_zero₂₁_le_left [Finite l] (A : Matrix l n R) (B : Matrix l o R)
    (D : Matrix p o R) : (fromBlocks A B 0 D).rank ≤ A.rank + Fintype.card o := by
  classical
  have := Fintype.ofFinite l
  have hsplit : fromBlocks A B 0 D = fromBlocks A 0 0 0 + fromBlocks 0 B 0 D := by
    rw [fromBlocks_add]
    simp
  let P : Matrix (l ⊕ p) l R := of fun i j => if i = Sum.inl j then 1 else 0
  let Q : Matrix n (n ⊕ o) R := of fun j k => if k = Sum.inl j then 1 else 0
  have hL : fromBlocks A 0 0 0 = P * A * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, mul_apply, fromBlocks]
  let X : Matrix (l ⊕ p) o R := of fun i j => fromBlocks (0 : Matrix l n R) B 0 D i (Sum.inr j)
  let Y : Matrix o (n ⊕ o) R := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 B 0 D = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, mul_apply]
  have h1 : (fromBlocks A (0 : Matrix l o R) 0 (0 : Matrix p o R)).rank ≤ A.rank := by
    rw [hL]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have h2 : (fromBlocks (0 : Matrix l n R) B 0 D).rank ≤ Fintype.card o := by
    rw [hR]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  rw [hsplit]
  exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

/-- The rank of `fromBlocks A B 0 D` is at most the number of rows of `A` plus the rank
of `D`. -/
theorem rank_fromBlocks_zero₂₁_le_right [Fintype l] [Finite p] (A : Matrix l n R)
    (B : Matrix l o R) (D : Matrix p o R) :
    (fromBlocks A B 0 D).rank ≤ Fintype.card l + D.rank := by
  classical
  have := Fintype.ofFinite p
  have hsplit : fromBlocks A B 0 D = fromBlocks A B 0 0 + fromBlocks 0 0 0 D := by
    rw [fromBlocks_add]
    simp
  let X : Matrix (l ⊕ p) l R := of fun i j => if i = Sum.inl j then 1 else 0
  let Y : Matrix l (n ⊕ o) R :=
    of fun j k => fromBlocks A B (0 : Matrix p n R) (0 : Matrix p o R) (Sum.inl j) k
  have hL : fromBlocks A B 0 0 = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, mul_apply]
  let P : Matrix (l ⊕ p) p R := of fun i j => if i = Sum.inr j then 1 else 0
  let Q : Matrix o (n ⊕ o) R := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 0 0 D = P * D * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, mul_apply, fromBlocks]
  have h1 : (fromBlocks A B 0 (0 : Matrix p o R)).rank ≤ Fintype.card l := by
    rw [hL]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have h2 : (fromBlocks (0 : Matrix l n R) (0 : Matrix l o R) 0 D).rank ≤ D.rank := by
    rw [hR]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  rw [hsplit]
  exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

end RankAdd

end Matrix

set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to `cRank` then deprecate
theorem Matrix.rank_vecMulVec.{u} {K m n : Type u} [CommRing K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 := by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun', Fintype.card_ofSubsingleton, Nat.cast_one]
