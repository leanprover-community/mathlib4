/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.GelfandRadius
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique

/-!
# The Gelfand radius as an algebra norm

This file uses the Gelfand radius to define an algebra norm on finite extension of a normed field.
-/

@[expose] public section

section matrices

open scoped Matrix.Norms.Operator

-- PRed
theorem Matrix.nnnorm_apply_le_linfty_opNNNorm {α β γ : Type*} [SeminormedAddCommGroup γ]
    [Fintype α] [Fintype β] (M : Matrix α β γ) (i : α) (j : β) : ‖M i j‖₊ ≤ ‖M‖₊ := by
  grw [Matrix.linfty_opNNNorm_def, ← Finset.le_sup_of_le (by simp)] -- these grws cannot be combined
  grw [← Finset.single_le_sum (by simp) (by simp)]

-- PRed
theorem Matrix.norm_apply_le_linfty_opNorm {α β γ : Type*} [SeminormedAddCommGroup γ]
    [Fintype α] [Fintype β] (M : Matrix α β γ) (i : α) (j : β) : ‖M i j‖ ≤ ‖M‖ := by
  grw [← coe_nnnorm, nnnorm_apply_le_linfty_opNNNorm, coe_nnnorm]

theorem Matrix.linfty_opNorm_sum_le_card_mul
    {α β γ κ : Type*} [Fintype α] [Fintype β] [SeminormedAddCommGroup γ] [IsUltrametricDist γ]
    (M : κ → Matrix α β γ) (s : Finset κ) (B : ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, ‖M i‖ ≤ B) :
    ‖∑ k ∈ s, M k‖ ≤ Fintype.card β * B := by
  let B' : NNReal := NNReal.mk B hB
  have h i j k (hk : k ∈ s) : ‖M k i j‖₊ ≤ B' :=
    (nnnorm_apply_le_linfty_opNNNorm (M k) i j).trans (hM k hk)
  replace h i j : ‖∑ k ∈ s, M k i j‖₊ ≤ B' :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB (h i j)
  have h i j : ‖(∑ k ∈ s, M k) i j‖₊ ≤ B' := by grw [sum_apply, h]
  grw [linfty_opNorm_def, h, Finset.sup_const_le]
  simp [B']

theorem Matrix.linfty_opNorm_add_le_card_mul_max
    {α β γ : Type*} [SeminormedAddCommGroup γ] [IsUltrametricDist γ] [Fintype α] [Fintype β]
    (M N : Matrix α β γ) : ‖M + N‖ ≤ Fintype.card β * max ‖M‖ ‖N‖ := by
  simpa using linfty_opNorm_sum_le_card_mul (Bool.rec N M) Finset.univ _ (by simp) (by simp)

-- PRed
theorem Matrix.gelfandRadius_blockDiagonal {R m n : Type*} (M : n → Matrix m m R)
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [NormedCommRing R] :
    gelfandRadius (Matrix.blockDiagonal M) = ⨆ i, gelfandRadius (M i) := by
  rcases isEmpty_or_nonempty n
  · simp [Subsingleton.elim M 0]
  let s : Finset n := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  rw [← Finset.sup'_univ_eq_ciSup]
  refine tendsto_nhds_unique_of_forall (tendsto_gelfandRadius (blockDiagonal M))
    (Filter.Tendsto.finset_sup'_nhds_apply hs fun i hi ↦ tendsto_gelfandRadius (M i)) fun k ↦ ?_
  have h (x y : NNReal) : max (x : ℝ) y ^ (k : ℝ)⁻¹ = max (x ^ (k : ℝ)⁻¹) (y ^ (k : ℝ)⁻¹) := by
    simp [Real.rpow_max]
  rw [← blockDiagonal_pow, linfty_opNorm_blockDiagonal, Pi.pow_def, Pi.norm_def, ← s.sup'_eq_sup hs,
    s.apply_sup'_eq_sup'_comp hs (f := fun x ↦ ‖M x ^ k‖₊) (fun x ↦ (x : ℝ) ^ (k : ℝ)⁻¹) h]
  simp [Function.comp_def]

end matrices

variable (K L M : Type*) [NormedField K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional K M]

open scoped Matrix.Norms.Operator

/-- The spectral norm defined by the spectral radius limit `lim ‖x ^ k‖ ^ (1 / k)`. -/
noncomputable def gelfandRadiusNorm : AlgebraNorm K L where
  toFun x := gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x)
  map_zero' := by rw [map_zero, gelfandRadius_zero]
  add_le' x y := by grw [map_add, ((Commute.all x y).map _).gelfandRadius_add_le]
  neg' x := by rw [map_neg, gelfandRadius_neg]
  mul_le' x y := by grw [map_mul, ((Commute.all x y).map _).gelfandRadius_mul_le]
  eq_zero_of_map_eq_zero' x h := by
    have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
    have hx := ((Commute.inv_right_self₀ x).map
      (Algebra.leftMulMatrix (Module.finBasis K L))).gelfandRadius_mul_le
    contrapose! hx
    simp [← map_mul, h, hx]
  smul' x y := by rw [map_smul, gelfandRadius_smul]

variable {L} in
theorem gelfandRadiusNorm_def (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x) :=
  rfl

@[simp]
theorem gelfandRadiusNorm_one : gelfandRadiusNorm K L 1 = 1 := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  rw [gelfandRadiusNorm_def, map_one, gelfandRadius_one]

variable {K} in
@[simp]
theorem gelfandRadiusNorm_eq_norm (x : K) : gelfandRadiusNorm K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (gelfandRadiusNorm K K) x 1

theorem isPowMul_gelfandRadiusNorm : IsPowMul (gelfandRadiusNorm K L) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  intro x k hk
  simp_rw [gelfandRadiusNorm_def, map_pow, gelfandRadius_pow]

variable {K L} in
theorem Module.Basis.gelfandRadiusNorm_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix b x) := by
  simp_rw [gelfandRadiusNorm_def, Algebra.leftMulMatrix_apply]
  rw [← basis_toMatrix_mul_linearMap_toMatrix b b (Module.finBasis K L),
    Matrix.gelfandRadius_mul_comm, linearMap_toMatrix_mul_basis_toMatrix]

@[simp]
theorem gelfandRadiusNorm_algebraMap (x : L) :
    gelfandRadiusNorm K M (algebraMap L M x) = gelfandRadiusNorm K L x := by
  have : FiniteDimensional L M := .of_restrictScalars_finite K L M
  have : NeZero (Module.finrank L M) := ⟨Module.finrank_pos.ne'⟩
  let bKL := Module.finBasis K L
  let bLM := Module.finBasis L M
  rw [(bKL.smulTower bLM).gelfandRadiusNorm_apply, Algebra.smulTower_leftMulMatrix_algebraMap,
    Matrix.gelfandRadius_blockDiagonal, ciSup_const, bKL.gelfandRadiusNorm_apply]

open Filter Topology in
theorem isNonarchimedean_gelfandRadiusNorm {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    [IsUltrametricDist K] [FiniteDimensional K L] : IsNonarchimedean (gelfandRadiusNorm K L) := by
  intro x y
  simp_rw [gelfandRadiusNorm_def]
  set T := Algebra.leftMulMatrix (Module.finBasis K L)
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have hr' : 0 ≤ r := by grind [gelfandRadius_nonneg]
  rw [max_lt_iff] at hr
  obtain ⟨Cx, hCx0, hCx⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (T x) hr.1
  obtain ⟨Cy, hCy0, hCy⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (T y) hr.2
  refine gelfandRadius_le_of_bound (C := Cx * Cy * Module.finrank K L) hr' fun n ↦ ?_
  suffices ∀ i ∈ Finset.range (n + 1), ‖T x ^ i * T y ^ (n - i) * (n.choose i)‖ ≤ Cx * Cy * r ^ n by
    grw [mul_assoc, mul_left_comm, map_add, ((Commute.all x y).map T).add_pow,
      Matrix.linfty_opNorm_sum_le_card_mul _ _ _ (by positivity) this, Fintype.card_fin]
  intro k hk
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  grw [norm_mul_le, norm_mul_le, hCx, hCy, ← map_natCast (algebraMap K _), norm_algebraMap',
    IsUltrametricDist.norm_natCast_le_one, mul_one,
    mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' (Finset.mem_range_succ_iff.mp hk)]
