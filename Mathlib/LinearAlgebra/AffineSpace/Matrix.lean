/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.Determinant

#align_import linear_algebra.affine_space.matrix from "leanprover-community/mathlib"@"2de9c37fa71dde2f1c6feff19876dd6a7b1519f0"

/-!
# Matrix results for barycentric co-ordinates

Results about the matrix of barycentric co-ordinates for a family of points in an affine space, with
respect to some affine basis.
-/


open Affine BigOperators Matrix

open Set

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `Basis.toMatrix`. -/
noncomputable def toMatrix {ι' : Type*} (q : ι' → P) : Matrix ι' ι k :=
  fun i j => b.coord j (q i)
#align affine_basis.to_matrix AffineBasis.toMatrix

@[simp]
theorem toMatrix_apply {ι' : Type*} (q : ι' → P) (i : ι') (j : ι) :
    b.toMatrix q i j = b.coord j (q i) := rfl
#align affine_basis.to_matrix_apply AffineBasis.toMatrix_apply

@[simp]
theorem toMatrix_self [DecidableEq ι] : b.toMatrix b = (1 : Matrix ι ι k) := by
  ext i j
  -- ⊢ toMatrix b (↑b) i j = OfNat.ofNat 1 i j
  rw [toMatrix_apply, coord_apply, Matrix.one_eq_pi_single, Pi.single_apply]
  -- 🎉 no goals
#align affine_basis.to_matrix_self AffineBasis.toMatrix_self

variable {ι' : Type*} [Fintype ι'] [Fintype ι] (b₂ : AffineBasis ι k P)

theorem toMatrix_row_sum_one {ι' : Type*} (q : ι' → P) (i : ι') : ∑ j, b.toMatrix q i j = 1 := by
  simp
  -- 🎉 no goals
#align affine_basis.to_matrix_row_sum_one AffineBasis.toMatrix_row_sum_one

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
theorem affineIndependent_of_toMatrix_right_inv [DecidableEq ι'] (p : ι' → P) {A : Matrix ι ι' k}
    (hA : b.toMatrix p * A = 1) : AffineIndependent k p := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  -- ⊢ ∀ (w1 w2 : ι' → k), ∑ i : ι', w1 i = 1 → ∑ i : ι', w2 i = 1 → ↑(Finset.affin …
  intro w₁ w₂ hw₁ hw₂ hweq
  -- ⊢ w₁ = w₂
  have hweq' : (b.toMatrix p).vecMul w₁ = (b.toMatrix p).vecMul w₂ := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    -- Porting note: Added `u` because `∘` was causing trouble
    have u : (fun i => b.coord j (p i)) = b.coord j ∘ p := by simp only [(· ∘ ·)]
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw₁,
      ← Finset.univ.affineCombination_eq_linear_combination _ _ hw₂, u,
      ← Finset.univ.map_affineCombination p w₁ hw₁, ← Finset.univ.map_affineCombination p w₂ hw₂,
      hweq]
  replace hweq' := congr_arg (fun w => A.vecMul w) hweq'
  -- ⊢ w₁ = w₂
  simpa only [Matrix.vecMul_vecMul, hA, Matrix.vecMul_one] using hweq'
  -- 🎉 no goals
#align affine_basis.affine_independent_of_to_matrix_right_inv AffineBasis.affineIndependent_of_toMatrix_right_inv

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entire space. -/
theorem affineSpan_eq_top_of_toMatrix_left_inv [DecidableEq ι] [Nontrivial k] (p : ι' → P)
    {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1) : affineSpan k (range p) = ⊤ := by
  suffices ∀ i, b i ∈ affineSpan k (range p) by
    rw [eq_top_iff, ← b.tot, affineSpan_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  -- ⊢ ↑b i ∈ affineSpan k (range p)
  have hAi : ∑ j, A i j = 1 := by
    calc
      ∑ j, A i j = ∑ j, A i j * ∑ l, b.toMatrix p j l := by simp
      _ = ∑ j, ∑ l, A i j * b.toMatrix p j l := by simp_rw [Finset.mul_sum]
      _ = ∑ l, ∑ j, A i j * b.toMatrix p j l := by rw [Finset.sum_comm]
      _ = ∑ l, (A * b.toMatrix p) i l := rfl
      _ = 1 := by simp [hA, Matrix.one_apply, Finset.filter_eq]
  have hbi : b i = Finset.univ.affineCombination k p (A i) := by
    apply b.ext_elem
    intro j
    rw [b.coord_apply, Finset.univ.map_affineCombination _ _ hAi,
      Finset.univ.affineCombination_eq_linear_combination _ _ hAi]
    change _ = (A * b.toMatrix p) i j
    simp_rw [hA, Matrix.one_apply, @eq_comm _ i j]
  rw [hbi]
  -- ⊢ ↑(Finset.affineCombination k Finset.univ p) (A i) ∈ affineSpan k (range p)
  exact affineCombination_mem_affineSpan hAi p
  -- 🎉 no goals
#align affine_basis.affine_span_eq_top_of_to_matrix_left_inv AffineBasis.affineSpan_eq_top_of_toMatrix_left_inv

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_inv_vecMul_toMatrix`. -/
@[simp]
theorem toMatrix_vecMul_coords (x : P) : (b.toMatrix b₂).vecMul (b₂.coords x) = b.coords x := by
  ext j
  -- ⊢ vecMul (↑(coords b₂) x) (toMatrix b ↑b₂) j = ↑(coords b) x j
  change _ = b.coord j x
  -- ⊢ vecMul (↑(coords b₂) x) (toMatrix b ↑b₂) j = ↑(coord b j) x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  -- ⊢ vecMul (↑(coords b₂) x) (toMatrix b ↑b₂) j = ↑(coord b j) (↑(Finset.affineCo …
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  -- ⊢ vecMul (↑(coords b₂) x) (toMatrix b ↑b₂) j = ↑(Finset.affineCombination ((fu …
  simp [Matrix.vecMul, Matrix.dotProduct, toMatrix_apply, coords]
  -- 🎉 no goals
#align affine_basis.to_matrix_vec_mul_coords AffineBasis.toMatrix_vecMul_coords

variable [DecidableEq ι]

theorem toMatrix_mul_toMatrix : b.toMatrix b₂ * b₂.toMatrix b = 1 := by
  ext l m
  -- ⊢ (toMatrix b ↑b₂ * toMatrix b₂ ↑b) l m = OfNat.ofNat 1 l m
  change (b₂.toMatrix b).vecMul (b.coords (b₂ l)) m = _
  -- ⊢ vecMul (↑(coords b) (↑b₂ l)) (toMatrix b₂ ↑b) m = OfNat.ofNat 1 l m
  rw [toMatrix_vecMul_coords, coords_apply, ← toMatrix_apply, toMatrix_self]
  -- 🎉 no goals
#align affine_basis.to_matrix_mul_to_matrix AffineBasis.toMatrix_mul_toMatrix

theorem isUnit_toMatrix : IsUnit (b.toMatrix b₂) :=
  ⟨{  val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := b.toMatrix_mul_toMatrix b₂
      inv_val := b₂.toMatrix_mul_toMatrix b }, rfl⟩
#align affine_basis.is_unit_to_matrix AffineBasis.isUnit_toMatrix

theorem isUnit_toMatrix_iff [Nontrivial k] (p : ι → P) :
    IsUnit (b.toMatrix p) ↔ AffineIndependent k p ∧ affineSpan k (range p) = ⊤ := by
  constructor
  -- ⊢ IsUnit (toMatrix b p) → AffineIndependent k p ∧ affineSpan k (range p) = ⊤
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.toMatrix p⟩
    -- ⊢ AffineIndependent k p ∧ affineSpan k (range p) = ⊤
    exact ⟨b.affineIndependent_of_toMatrix_right_inv p hA,
      b.affineSpan_eq_top_of_toMatrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    -- ⊢ IsUnit (toMatrix b p)
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    -- ⊢ IsUnit (toMatrix b p)
    change IsUnit (b.toMatrix b')
    -- ⊢ IsUnit (toMatrix b ↑b')
    exact b.isUnit_toMatrix b'
    -- 🎉 no goals
#align affine_basis.is_unit_to_matrix_iff AffineBasis.isUnit_toMatrix_iff

end Ring

section CommRing

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]

variable (b b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `AffineBasis.toMatrix_vecMul_coords`. -/
@[simp]
theorem toMatrix_inv_vecMul_toMatrix (x : P) :
    (b.toMatrix b₂)⁻¹.vecMul (b.coords x) = b₂.coords x := by
  have hu := b.isUnit_toMatrix b₂
  -- ⊢ vecMul (↑(coords b) x) (toMatrix b ↑b₂)⁻¹ = ↑(coords b₂) x
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  -- ⊢ vecMul (↑(coords b) x) (toMatrix b ↑b₂)⁻¹ = ↑(coords b₂) x
  rw [← b.toMatrix_vecMul_coords b₂, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
    Matrix.vecMul_one]
#align affine_basis.to_matrix_inv_vec_mul_to_matrix AffineBasis.toMatrix_inv_vecMul_toMatrix

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
theorem det_smul_coords_eq_cramer_coords (x : P) :
    (b.toMatrix b₂).det • b₂.coords x = (b.toMatrix b₂)ᵀ.cramer (b.coords x) := by
  have hu := b.isUnit_toMatrix b₂
  -- ⊢ det (toMatrix b ↑b₂) • ↑(coords b₂) x = ↑(cramer (toMatrix b ↑b₂)ᵀ) (↑(coord …
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  -- ⊢ det (toMatrix b ↑b₂) • ↑(coords b₂) x = ↑(cramer (toMatrix b ↑b₂)ᵀ) (↑(coord …
  rw [← b.toMatrix_inv_vecMul_toMatrix, Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]
  -- 🎉 no goals
#align affine_basis.det_smul_coords_eq_cramer_coords AffineBasis.det_smul_coords_eq_cramer_coords

end CommRing

end AffineBasis
