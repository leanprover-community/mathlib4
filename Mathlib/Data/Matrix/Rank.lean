/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix
* `Matrix.cRank`: the rank of a matrix as a cardinal
* `Matrix.eRank`: the rank of a matrix as a term in `ℕ∞`.

-/

open Matrix

namespace Matrix

open Module Cardinal Set Submodule

universe ul um um₀ un un₀ uo uR
variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}
variable {R : Type uR}

section Infinite

variable [Semiring R]

/-- The rank of a matrix, defined as the dimension of its column space, as a cardinal. -/
noncomputable def cRank (A : Matrix m n R) : Cardinal := Module.rank R <| span R <| range Aᵀ

lemma cRank_toNat_eq_finrank (A : Matrix m n R) :
    A.cRank.toNat = Module.finrank R (span R (range A.col)) := rfl

lemma lift_cRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    lift.{um} (A.submatrix r c).cRank ≤ lift.{um₀} A.cRank := by
  have h : ((A.submatrix r id).submatrix id c).cRank ≤ (A.submatrix r id).cRank :=
    Submodule.rank_mono <| span_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩
  refine (Cardinal.lift_monotone h).trans ?_
  let f : (m → R) →ₗ[R] (m₀ → R) := LinearMap.funLeft R R r
  have h_eq : Submodule.map f (span R (range Aᵀ)) = span R (range (A.submatrix r id)ᵀ) := by
    rw [LinearMap.map_span, ← image_univ, image_image, transpose_submatrix]
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
  (rank_span_le ..).trans <| by simpa using Cardinal.mk_range_le_lift (f := Aᵀ)

/-- The rank of a matrix, defined as the dimension of its column space, as a term in `ℕ∞`. -/
noncomputable def eRank (A : Matrix m n R) : ℕ∞ := A.cRank.toENat

lemma eRank_toNat_eq_finrank (A : Matrix m n R) :
    A.eRank.toNat = Module.finrank R (span R (range A.col)) :=
  toNat_toENat ..

lemma eRank_submatrix_le (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :
    (A.submatrix r c).eRank ≤ A.eRank := by
  simpa using OrderHom.mono (β := ℕ∞) Cardinal.toENat <| lift_cRank_submatrix_le A r c

lemma eRank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card n := by
  wlog hfin : Finite n
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite n
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_nat]
  exact A.cRank_le_card_width

lemma eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card m := by
  classical
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card, eRank, toENat_le_nat]
  exact A.cRank_le_card_height

end Infinite

variable [Fintype n] [Fintype o]

section CommRing

variable [CommRing R]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : Matrix m n R) : ℕ :=
  finrank R <| LinearMap.range A.mulVecLin

@[simp]
theorem cRank_one [StrongRankCondition R] [DecidableEq m] :
    (cRank (1 : Matrix m m R)) = lift.{uR} #m := by
  have := nontrivial_of_invariantBasisNumber R
  have h : LinearIndependent R (1 : Matrix m m R)ᵀ := by
    convert Pi.linearIndependent_single_one m R
    simp [funext_iff, Matrix.one_eq_pi_single]
  rw [cRank, rank_span h, ← lift_umax, ← Cardinal.mk_range_eq_of_injective h.injective, lift_id']

@[simp] theorem eRank_one [StrongRankCondition R] [DecidableEq m] :
    (eRank (1 : Matrix m m R)) = ENat.card m := by
  rw [eRank, cRank_one, toENat_lift, ENat.card]

@[simp]
theorem rank_one [StrongRankCondition R] [DecidableEq n] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, mulVecLin_one, LinearMap.range_id, finrank_top, finrank_pi]

@[simp]
theorem rank_zero [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, mulVecLin_zero, LinearMap.range_zero, finrank_bot]

@[simp]
theorem cRank_zero {m n : Type*} [Nontrivial R] : cRank (0 : Matrix m n R) = 0 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [cRank, range_eq_empty, span_empty, rank_bot]
  rw [cRank, transpose_zero, range_zero, span_zero_singleton, rank_bot]

@[simp]
theorem eRank_zero {m n : Type*} [Nontrivial R] : eRank (0 : Matrix m n R) = 0 := by
  simp [eRank]

theorem rank_le_card_width [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card n := by
  haveI : Module.Finite R (n → R) := Module.Finite.pi
  haveI : Module.Free R (n → R) := Module.Free.pi _ _
  exact A.mulVecLin.finrank_range_le.trans_eq (finrank_pi _)

theorem rank_le_width [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le

theorem rank_mul_le_left [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ A.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left _ _) (rank_lt_aleph0 _ _)

theorem rank_mul_le_right [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ B.rank := by
  rw [rank, rank, mulVecLin_mul]
  exact finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _)
    (rank_lt_aleph0 _ _)

theorem rank_mul_le [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

theorem rank_unit [StrongRankCondition R] [DecidableEq n] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n := by
  apply le_antisymm (rank_le_card_width (A : Matrix n n R)) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, rank_one] at this

theorem rank_of_isUnit [StrongRankCondition R] [DecidableEq n] (A : Matrix n n R) (h : IsUnit A) :
    A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A

/-- Right multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_left_of_isUnit_det [DecidableEq n]
    (A : Matrix n n R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (B * A).rank = B.rank := by
  suffices Function.Surjective A.mulVecLin by
    rw [rank, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr this), ← rank]
  intro v
  exact ⟨(A⁻¹).mulVecLin v, by simp [mul_nonsing_inv _ hA]⟩

/-- Left multiplying by an invertible matrix does not change the rank -/
@[simp]
lemma rank_mul_eq_right_of_isUnit_det [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix m n R) (hA : IsUnit A.det) :
    (A * B).rank = B.rank := by
  let b : Basis m R (m → R) := Pi.basisFun R m
  replace hA : IsUnit (LinearMap.toMatrix b b A.mulVecLin).det := by
    convert hA; rw [← LinearEquiv.eq_symm_apply]; rfl
  have hAB : mulVecLin (A * B) = (LinearEquiv.ofIsUnitDet hA).comp (mulVecLin B) := by ext; simp
  rw [rank, rank, hAB, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

/-- Taking a subset of the rows and permuting the columns reduces the rank. -/
theorem rank_submatrix_le [StrongRankCondition R] [Fintype m] (f : n → m) (e : n ≃ m)
    (A : Matrix m m R) : rank (A.submatrix f e) ≤ rank A := by
  rw [rank, rank, mulVecLin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R e.symm = LinearEquiv.funCongrLeft R R e.symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _

theorem rank_reindex [Fintype n₀] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) :
    rank (A.reindex em en) = rank A := by
  rw [rank, rank, mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

@[simp]
theorem rank_submatrix [Fintype n₀] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    rank (A.submatrix em en) = rank A := by
  simpa only [reindex_apply] using rank_reindex em.symm en.symm A

@[simp]
theorem lift_cRank_submatrix {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    lift.{um} (cRank (A.submatrix em en)) = lift.{um₀} (cRank A) :=
  (A.lift_cRank_submatrix_le em en).antisymm
    <| by simpa using ((A.reindex em.symm en.symm).lift_cRank_submatrix_le em.symm en.symm)

/-- A special case of `lift_cRank_submatrix` for when the row types are in the same universe. -/
@[simp]
theorem cRank_submatrix {m₀ : Type um} {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : cRank (A.submatrix em en) = cRank A := by
  simpa [-lift_cRank_submatrix] using A.lift_cRank_submatrix em en

theorem lift_cRank_reindex {n : Type un} (A : Matrix m n R) (em : m ≃ m₀) (en : n ≃ n₀) :
    lift.{um} (cRank (A.reindex em en)) = lift.{um₀} (cRank A) :=
  lift_cRank_submatrix ..

/-- A special case of `lift_cRank_reindex` for when the row types are in the same universe. -/
theorem cRank_reindex {m₀ : Type um} {n : Type un} (A : Matrix m n R) (em : m ≃ m₀) (en : n ≃ n₀) :
    cRank (A.reindex em en) = cRank A :=
  cRank_submatrix ..

@[simp]
theorem eRank_submatrix {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    eRank (A.submatrix em en) = eRank A := by
  simpa [-lift_cRank_submatrix] using congr_arg Cardinal.toENat <| A.lift_cRank_submatrix em en

theorem eRank_reindex {m₀ : Type um} {n : Type un} (A : Matrix m n R) (em : m ≃ m₀) (en : n ≃ n₀) :
    eRank (A.reindex em en) = eRank A :=
  eRank_submatrix ..

theorem rank_eq_finrank_range_toLin [Finite m] [DecidableEq n] {M₁ M₂ : Type*} [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R) (v₁ : Basis m R M₁)
    (v₂ : Basis n R M₂) : A.rank = finrank R (LinearMap.range (toLin v₂ v₁ A)) := by
  cases nonempty_fintype m
  let e₁ := (Pi.basisFun R m).equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).equiv v₂ (Equiv.refl _)
  have range_e₂ : LinearMap.range e₂ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine LinearEquiv.finrank_eq (e₁.ofSubmodules _ _ ?_)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (toLin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := toLin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [toLin_eq_toLin', toLin'_apply'] at aux₁
  rw [Pi.basisFun_apply] at aux₁ aux₂
  simp only [e₁, e₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.refl_apply,
    aux₁, aux₂, LinearMap.coe_single, toLin_self, map_sum, LinearEquiv.map_smul, Basis.equiv_apply]

theorem rank_le_card_height [Fintype m] [StrongRankCondition R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card m := by
  haveI : Module.Finite R (m → R) := Module.Finite.pi
  haveI : Module.Free R (m → R) := Module.Free.pi _ _
  exact (Submodule.finrank_le _).trans (finrank_pi R).le

theorem rank_le_height [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ m :=
  A.rank_le_card_height.trans <| (Fintype.card_fin m).le

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
theorem rank_eq_finrank_span_cols (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range A.col)) := by rw [rank, Matrix.range_mulVecLin]

@[simp]
theorem cRank_toNat_eq_rank (A : Matrix m n R) : A.cRank.toNat = A.rank := by
  rw [cRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

@[simp]
theorem eRank_toNat_eq_rank (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [eRank_toNat_eq_finrank, ← rank_eq_finrank_span_cols]

end CommRing

section Field

variable [Field R]

/-- The rank of a diagonal matrix is the count of non-zero elements on its main diagonal -/
theorem rank_diagonal [Fintype m] [DecidableEq m] [DecidableEq R] (w : m → R) :
    (diagonal w).rank = Fintype.card {i // (w i) ≠ 0} := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', Module.finrank, ← LinearMap.rank,
    LinearMap.rank_diagonal, Cardinal.toNat_natCast]

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
  have hrw : insert 0 (range (diagonal w)ᵀ) = insert 0 (range w') := by
    suffices ∀ a, diagonal w a = 0 ∨ ∃ b, w b ≠ 0 ∧ diagonal w b = diagonal w a
      by simpa [subset_antisymm_iff, subset_def, w']
    simp_rw [or_iff_not_imp_right, not_exists, not_and, not_imp_not]
    simp +contextual [funext_iff, diagonal, or_iff_not_imp_right]
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
    replace h := congr_arg (dotProduct x) h
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

end Matrix
