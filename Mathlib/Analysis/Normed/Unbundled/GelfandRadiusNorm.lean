/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.GelfandRadius
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique

/-!
# The Gelfand radius as an algebra norm

This file uses the Gelfand radius to define an algebra norm on a finite extension of a normed field.

## Main definitions

* `gelfandRadiusNormAux K L`: The algebra norm on a finite extension `L` of a normed field `K`.
  The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`.

## Main statements

* `isPowMul_gelfandRadiusNormAux`: the Gelfand radius norm is power-multiplicative.
* `gelfandRadiusNormAux_algebraMap`: the Gelfand radius norm is invariant under algebra maps.
* `gelfandRadiusNormAux_map`: the Gelfand radius norm is invariant under algebra homomorphisms.
-/

variable (K L M : Type*) [NormedField K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M]

section

section matrices

open scoped Matrix.Norms.Operator

-- PRed
theorem Matrix.linfty_opNNNorm_sum_le_card_mul_of_forall_le
    {α β γ κ : Type*} [Fintype α] [Fintype β] [SeminormedAddCommGroup γ] [IsUltrametricDist γ]
    (M : κ → Matrix α β γ) (s : Finset κ) (B : NNReal) (hM : ∀ i ∈ s, ‖M i‖₊ ≤ B) :
    ‖∑ k ∈ s, M k‖₊ ≤ Fintype.card β * B := by
  sorry

-- PRed
theorem Matrix.linfty_opNorm_sum_le_card_mul_of_forall_le
    {α β γ κ : Type*} [Fintype α] [Fintype β] [SeminormedAddCommGroup γ] [IsUltrametricDist γ]
    (M : κ → Matrix α β γ) (s : Finset κ) (B : ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, ‖M i‖ ≤ B) :
    ‖∑ k ∈ s, M k‖ ≤ Fintype.card β * B :=
  sorry

end matrices

variable [FiniteDimensional K L] [FiniteDimensional K M]

private local instance [FiniteDimensional L M] : NeZero (Module.finrank L M) :=
  ⟨Module.finrank_pos.ne'⟩

open scoped Matrix.Norms.Operator

/-- The Gelfand radius algebra norm on a finite extension `L` of a normed field `K`.
The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`. -/
noncomputable def gelfandRadiusNormAux : AlgebraNorm K L where
  toFun x := gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x)
  map_zero' := by rw [map_zero, gelfandRadius_zero]
  add_le' x y := by grw [map_add, ((Commute.all x y).map _).gelfandRadius_add_le]
  neg' x := by rw [map_neg, gelfandRadius_neg]
  mul_le' x y := by grw [map_mul, ((Commute.all x y).map _).gelfandRadius_mul_le]
  eq_zero_of_map_eq_zero' x h := by
    have hx := ((Commute.inv_right_self₀ x).map
      (Algebra.leftMulMatrix (Module.finBasis K L))).gelfandRadius_mul_le
    contrapose! hx
    simp [← map_mul, h, hx]
  smul' x y := by rw [map_smul, gelfandRadius_smul]

variable {L} in
/-- The Gelfand radius norm of `x : L` is the Gelfand radius of multiplication of `x` on `L`.
See `Module.Basis.gelfandRadiusNormAux_apply` for a version taking an arbitrary `K`-basis of `L`. -/
theorem gelfandRadiusNormAux_def (x : L) :
    gelfandRadiusNormAux K L x = gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x) := by
  rfl

@[simp]
theorem gelfandRadiusNormAux_one : gelfandRadiusNormAux K L 1 = 1 := by
  rw [gelfandRadiusNormAux_def, map_one, gelfandRadius_one]

variable {K} in
@[simp]
theorem gelfandRadiusNormAux_eq_norm (x : K) : gelfandRadiusNormAux K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (gelfandRadiusNormAux K K) x 1

/-- The Gelfand radius norm is power-multiplicative. -/
theorem isPowMul_gelfandRadiusNormAux : IsPowMul (gelfandRadiusNormAux K L) := by
  intro x k hk
  simp_rw [gelfandRadiusNormAux_def, map_pow, gelfandRadius_pow]

variable {K L} in
theorem Module.Basis.gelfandRadiusNormAux_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (x : L) :
    gelfandRadiusNormAux K L x = gelfandRadius (Algebra.leftMulMatrix b x) :=
  ((Algebra.lmul K L) x).gelfandRadius_toMatrix_eq (finBasis K L) b

variable {L} in
/-- The Gelfand radius norm is invariant under algebra maps. -/
@[simp]
theorem gelfandRadiusNormAux_algebraMap (x : L) :
    gelfandRadiusNormAux K M (algebraMap L M x) = gelfandRadiusNormAux K L x := by
  have : FiniteDimensional L M := .of_restrictScalars_finite K L M
  let bKL := Module.finBasis K L
  let bLM := Module.finBasis L M
  rw [(bKL.smulTower bLM).gelfandRadiusNormAux_apply, Algebra.smulTower_leftMulMatrix_algebraMap,
    Matrix.gelfandRadius_blockDiagonal, ciSup_const, bKL.gelfandRadiusNormAux_apply]

variable {M K L} in
omit [Algebra L M] [IsScalarTower K L M] in
/-- The Gelfand radius norm is invariant under algebra homomorphisms. -/
@[simp]
theorem gelfandRadiusNormAux_map {F : Type*} [FunLike F L M] [AlgHomClass F K L M] (f : F) (x : L) :
    gelfandRadiusNormAux K M (f x) = gelfandRadiusNormAux K L x :=
  let := (AlgHom.ofClass f).toAlgebra
  gelfandRadiusNormAux_algebraMap K M x

open Filter Topology in
theorem isNonarchimedean_gelfandRadiusNormAux [IsUltrametricDist K] :
    IsNonarchimedean (gelfandRadiusNormAux K L) := by
  intro x y
  simp_rw [gelfandRadiusNormAux_def]
  set T := Algebra.leftMulMatrix (Module.finBasis K L)
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have hr' : 0 ≤ r := by grind [gelfandRadius_nonneg]
  rw [max_lt_iff] at hr
  obtain ⟨Cx, hCx0, hCx⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (T x) hr.1
  obtain ⟨Cy, hCy0, hCy⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (T y) hr.2
  refine gelfandRadius_le_of_bound (C := Cx * Cy * Module.finrank K L) hr' fun n ↦ ?_
  suffices ∀ i ∈ Finset.range (n + 1), ‖T x ^ i * T y ^ (n - i) * (n.choose i)‖ ≤ Cx * Cy * r ^ n by
    grw [mul_assoc, mul_left_comm, map_add, ((Commute.all x y).map T).add_pow,
      Matrix.linfty_opNorm_sum_le_card_mul_of_forall_le _ _ _ (by positivity) this,
        Fintype.card_fin]
  intro k hk
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  grw [norm_mul_le, norm_mul_le, hCx, hCy, ← map_natCast (algebraMap K _), norm_algebraMap',
    IsUltrametricDist.norm_natCast_le_one, mul_one,
    mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' (Finset.mem_range_succ_iff.mp hk)]

end

public section

section gelfandRadiusNorm

open IntermediateField

open Classical in
/-- This will eventually replace `gelfandRadiusNorm`. -/
noncomputable def gelfandRadiusNorm (x : L) : ℝ :=
  if hx : IsAlgebraic K x then
    haveI := adjoin.finiteDimensional hx.isIntegral
    gelfandRadiusNormAux K K⟮x⟯ (AdjoinSimple.gen K x)
  else 0

variable {K L} in
theorem gelfandRadiusNorm_eq_zero {x : L} (hx : ¬ IsAlgebraic K x) : gelfandRadiusNorm K L x = 0 :=
  dite_eq_right hx

private theorem IsAlgebraic.gelfandRadiusNorm_eq {x : L} (hx : IsAlgebraic K x) :
    haveI := adjoin.finiteDimensional hx.isIntegral
    gelfandRadiusNorm K L x = gelfandRadiusNormAux K K⟮x⟯ (AdjoinSimple.gen K x) :=
  dite_eq_left hx

private theorem FiniteDimensional.gelfandRadiusNorm_eq [FiniteDimensional K L] (x : L) :
    gelfandRadiusNorm K L x = gelfandRadiusNormAux K L x :=
  (Algebra.IsAlgebraic.isAlgebraic x).gelfandRadiusNorm_eq.trans
    (gelfandRadiusNormAux_algebraMap K L (AdjoinSimple.gen K x)).symm

@[simp]
theorem gelfandRadiusNorm_algebraMap (x : L) :
    gelfandRadiusNorm K M (algebraMap L M x) = gelfandRadiusNorm K L x := by
  by_cases hx : IsAlgebraic K x
  · rw [hx.gelfandRadiusNorm_eq, hx.algebraMap.gelfandRadiusNorm_eq]
    let f := IsScalarTower.toAlgHom K L M
    have hf : K⟮x⟯.map f = K⟮algebraMap L M x⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IsScalarTower.toAlgHom_apply]
    let g : K⟮x⟯ →ₐ[K] K⟮algebraMap L M x⟯ := (equivMap K⟮x⟯ f).trans (equivOfEq hf)
    let := g.toRingHom.toAlgebra
    have := adjoin.finiteDimensional hx.isIntegral
    have : FiniteDimensional K K⟮algebraMap L M x⟯ :=
      adjoin.finiteDimensional hx.algebraMap.isIntegral
    exact gelfandRadiusNormAux_algebraMap K (K⟮algebraMap L M x⟯) (AdjoinSimple.gen K x)
  · rw [gelfandRadiusNorm_eq_zero hx, gelfandRadiusNorm_eq_zero]
    exact mt (isAlgebraic_algebraMap_iff (algebraMap L M).injective).mp hx

variable {K L} in
private theorem IntermediateField.gelfandRadiusNorm_eq
    (E : IntermediateField K L) [FiniteDimensional K E]
    (x : L) (y : E) (h : x = y) : gelfandRadiusNorm K L x = gelfandRadiusNormAux K E y := by
  rw [h, ← E.algebraMap_apply, gelfandRadiusNorm_algebraMap, FiniteDimensional.gelfandRadiusNorm_eq]

@[simp]
theorem gelfandRadiusNorm_zero : gelfandRadiusNorm K L 0 = 0 := by
  rw [IntermediateField.gelfandRadiusNorm_eq ⊥ 0 0 rfl, map_zero]

@[simp]
theorem gelfandRadiusNorm_one : gelfandRadiusNorm K L 1 = 1 := by
  rw [IntermediateField.gelfandRadiusNorm_eq ⊥ 1 1 rfl, gelfandRadiusNormAux_one]

variable {L} in
@[simp]
theorem gelfandRadiusNorm_neg (x : L) : gelfandRadiusNorm K L (-x) = gelfandRadiusNorm K L x := by
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [K⟮x⟯.gelfandRadiusNorm_eq x (AdjoinSimple.gen K x) rfl,
      K⟮x⟯.gelfandRadiusNorm_eq (-x) (-AdjoinSimple.gen K x) rfl, map_neg_eq_map]
  · rw [gelfandRadiusNorm_eq_zero, gelfandRadiusNorm_eq_zero hx]
    contrapose hx
    simpa using hx.neg

variable {K L} in
@[simp]
theorem gelfandRadiusNorm_smul (x : K) (y : L) :
    gelfandRadiusNorm K L (x • y) = ‖x‖ * gelfandRadiusNorm K L y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : IsAlgebraic K y
  · have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional hy.isIntegral
    rw [K⟮y⟯.gelfandRadiusNorm_eq y (AdjoinSimple.gen K y) rfl,
      K⟮y⟯.gelfandRadiusNorm_eq (x • y) (x • AdjoinSimple.gen K y) rfl, map_smul_eq_mul]
  · rw [gelfandRadiusNorm_eq_zero, gelfandRadiusNorm_eq_zero hy, mul_zero]
    contrapose hy
    simpa [hx] using hy.smul x⁻¹

variable {K} in
@[simp]
theorem gelfandRadiusNorm_eq_norm (x : K) : gelfandRadiusNorm K K x = ‖x‖ := by
  simpa using gelfandRadiusNorm_smul x (1 : K)

variable {K L} in
theorem gelfandRadiusNorm_add_le {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    gelfandRadiusNorm K L (x + y) ≤ gelfandRadiusNorm K L x + gelfandRadiusNorm K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [K⟮x, y⟯.gelfandRadiusNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq (x + y) (AdjoinPair.gen₁ K x y + AdjoinPair.gen₂ K x y) rfl]
  apply map_add_le_add

variable {K L} in
theorem gelfandRadiusNorm_mul_le {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    gelfandRadiusNorm K L (x * y) ≤ gelfandRadiusNorm K L x * gelfandRadiusNorm K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [K⟮x, y⟯.gelfandRadiusNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq (x * y) (AdjoinPair.gen₁ K x y * AdjoinPair.gen₂ K x y) rfl]
  apply map_mul_le_mul

variable {K L} in
theorem eq_zero_of_gelfandRadiusNorm_eq_zero {x : L} (hx : IsAlgebraic K x)
    (hx0 : gelfandRadiusNorm K L x = 0) : x = 0 := by
  rw [hx.gelfandRadiusNorm_eq] at hx0
  exact Subtype.ext_iff.mp (eq_zero_of_map_eq_zero _ hx0)

theorem isPowMul_gelfandRadiusNorm : IsPowMul (gelfandRadiusNorm K L) := by
  intro x k hk
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [K⟮x⟯.gelfandRadiusNorm_eq x (AdjoinSimple.gen K x) rfl,
      K⟮x⟯.gelfandRadiusNorm_eq (x ^ k) (AdjoinSimple.gen K x ^ k) rfl,
      isPowMul_gelfandRadiusNormAux K K⟮x⟯ (AdjoinSimple.gen K x) hk]
  · rw [gelfandRadiusNorm_eq_zero hx, gelfandRadiusNorm_eq_zero, zero_pow (by grind)]
    contrapose hx
    exact hx.of_pow hk

theorem isNonarchimedean_gelfandRadiusNorm {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    [IsUltrametricDist K] [Algebra.IsAlgebraic K L] : IsNonarchimedean (gelfandRadiusNorm K L) := by
  rw [IsNonarchimedean]
  intro x y
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
  rw [K⟮x, y⟯.gelfandRadiusNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.gelfandRadiusNorm_eq (x + y) (AdjoinPair.gen₁ K x y + AdjoinPair.gen₂ K x y) rfl]
  apply isNonarchimedean_gelfandRadiusNormAux

end gelfandRadiusNorm

section gelfandRadiusAlgNorm

variable [Algebra.IsAlgebraic K L]

open Algebra.IsAlgebraic in
/-- The spectral norm is a `K`-algebra norm on `L`. -/
noncomputable def gelfandRadiusAlgNorm : AlgebraNorm K L where
  toFun := gelfandRadiusNorm K L
  map_zero' := gelfandRadiusNorm_zero K L
  add_le' x y := gelfandRadiusNorm_add_le (isAlgebraic x) (isAlgebraic y)
  neg' := gelfandRadiusNorm_neg K
  mul_le' x y := gelfandRadiusNorm_mul_le (isAlgebraic x) (isAlgebraic y)
  eq_zero_of_map_eq_zero' x := eq_zero_of_gelfandRadiusNorm_eq_zero (isAlgebraic x)
  smul' := gelfandRadiusNorm_smul

theorem gelfandRadiusAlgNorm_def (x : L) : gelfandRadiusAlgNorm K L x = gelfandRadiusNorm K L x := by
  rfl

omit [Algebra.IsAlgebraic K L] in
variable [Algebra.IsAlgebraic K M] in
@[simp]
theorem gelfandRadiusAlgNorm_algebraMap (x : L) :
    haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
    gelfandRadiusAlgNorm K M (algebraMap L M x) = gelfandRadiusAlgNorm K L x :=
  gelfandRadiusNorm_algebraMap K L M x

@[simp]
theorem gelfandRadiusAlgNorm_one : gelfandRadiusAlgNorm K L (1 : L) = 1 :=
  gelfandRadiusNorm_one K L

@[simp]
theorem gelfandRadiusAlgNorm_eq_norm (x : K) : gelfandRadiusAlgNorm K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (gelfandRadiusAlgNorm K K) x 1

theorem isPowMul_gelfandRadiusAlgNorm : IsPowMul (gelfandRadiusAlgNorm K L) :=
  isPowMul_gelfandRadiusNorm K L

omit [Algebra L M] [IsScalarTower K L M] [Algebra.IsAlgebraic K L] in
@[simp]
theorem gelfandRadiusNorm_algHom {F : Type*} [FunLike F L M] [AlgHomClass F K L M] (σ : F) (x : L) :
    gelfandRadiusNorm K M (σ x) = gelfandRadiusNorm K L x :=
  let := (AlgHom.ofClass σ).toAlgebra
  gelfandRadiusNorm_algebraMap K L M x

end gelfandRadiusAlgNorm

end
