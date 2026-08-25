/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.SpectralRadiusLimit
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.InvariantExtension
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral norms and extensions of absolute values

This file defines spectral norms and uses them to construct extensions of absolute values.
-/

@[expose] public section

-- todo: golf `normFromConst` file

-- #42986
open Filter Topology in
theorem tendsto_nhds_unique_of_forall {X Y : Type*} [TopologicalSpace X] [T2Space X] {f g : Y → X}
    {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b))
    (hfg : ∀ y, f y = g y) : a = b :=
  tendsto_nhds_unique_of_eventuallyEq ha hb (Eventually.of_forall hfg)

section matrices

open scoped Matrix.Norms.Operator

-- #43016
theorem Matrix.linfty_opNNNorm_blockDiagonal
    {R m n o : Type*} [SeminormedAddCommGroup R]
    [DecidableEq o] [Fintype m] [Fintype n] [Fintype o] (M : o → Matrix m n R) :
    ‖blockDiagonal M‖₊ = ‖M‖₊ := by
  simp_rw [Pi.nnnorm_def, linfty_opNNNorm_def, ← Finset.univ_product_univ,
    Finset.sup_product_right, Finset.sum_product, blockDiagonal_apply, apply_ite]
  simp

-- ##43016
theorem Matrix.linfty_opNorm_blockDiagonal
    {R m n o : Type*} [SeminormedAddCommGroup R]
    [DecidableEq o] [Fintype m] [Fintype n] [Fintype o] (M : o → Matrix m n R) :
    ‖blockDiagonal M‖ = ‖M‖ :=
  congr_arg ((↑) : NNReal → Real) <| linfty_opNNNorm_blockDiagonal M

-- waiting on spectral radius (also look into futher golfing)
open Filter Topology in
private theorem Matrix.spectralRadiusLim_conj_le {R m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [NormedCommRing R]
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hAC : A * C = 1) (hCA : C * A = 1) : spectralRadiusLim (A * B * C) ≤ spectralRadiusLim B := by
  cases subsingleton_or_nontrivial (Matrix n n R)
  · simp [Subsingleton.elim B 0]
  have h k : (A * B * C) ^ k = A * B ^ k * C := by
    induction k with
    | zero => simp [hAC]
    | succ n ih => transitivity A * B ^ n * (C * A) * B * C <;> grind [Matrix.mul_assoc]
  suffices Tendsto (fun k : ℕ ↦ ‖A‖ ^ (k : ℝ)⁻¹ * ‖B ^ k‖ ^ (k : ℝ)⁻¹ * ‖C‖ ^ (k : ℝ)⁻¹) atTop
      (𝓝 (1 * spectralRadiusLim B * 1)) by
    rw [one_mul, mul_one] at this
    refine le_of_tendsto_of_tendsto' (tendsto_spectralRadiusLim (A * B * C)) this fun n ↦ ?_
    grw [h, Matrix.linfty_opNorm_mul, Matrix.linfty_opNorm_mul,
      Real.mul_rpow, Real.mul_rpow] <;> positivity
  have hA : ‖A‖ ≠ 0 := by contrapose! hCA; simp_all
  have hC : ‖C‖ ≠ 0 := by contrapose! hCA; simp_all
  have key {c : ℝ} (hc : c ≠ 0) :=
    ((Real.continuous_const_rpow hc).tendsto' 0 1 c.rpow_zero).comp tendsto_inv_atTop_nhds_zero_nat
  exact ((key hA).mul (tendsto_spectralRadiusLim B)).mul (key hC)

-- waiting on spectral radius (also look into futher golfing)
theorem Matrix.spectralRadiusLim_conj {R m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [NormedCommRing R]
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hAC : A * C = 1) (hCA : C * A = 1) : spectralRadiusLim (A * B * C) = spectralRadiusLim B := by
  refine le_antisymm (Matrix.spectralRadiusLim_conj_le A B C hAC hCA) ?_
  have h : C * (A * B * C) * A = B := by
    transitivity (C * A) * B * (C * A) <;> grind [Matrix.mul_assoc]
  have := Matrix.spectralRadiusLim_conj_le C (A * B * C) A hCA hAC
  rwa [h] at this

-- waiting on spectral radius
theorem Matrix.spectralRadiusLim_blockMatrix {R m : Type*} [DecidableEq m] [Fintype m]
    [NormedCommRing R] (A : Matrix m m R) (n : Type*) [DecidableEq n] [Fintype n] [Nonempty n] :
    spectralRadiusLim (Matrix.blockDiagonal fun _ : n ↦ A) = spectralRadiusLim A := by
  refine tendsto_nhds_unique_of_forall (tendsto_spectralRadiusLim (blockDiagonal fun _ ↦ A))
    (tendsto_spectralRadiusLim A) fun k ↦ ?_
  rw [← blockDiagonal_pow, Matrix.linfty_opNorm_blockDiagonal, Pi.pow_def, pi_norm_const]

end matrices

-- all blocked by spectral radius
section spectralRadiusLimNorm

variable (K L M : Type*) [NormedField K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional K M]

open scoped Matrix.Norms.Operator

/-- The spectral norm defined by the spectral radius limit `lim ‖x ^ k‖ ^ (1 / k)`. -/
noncomputable def spectralRadiusLimNorm : AlgebraNorm K L where
  toFun x := spectralRadiusLim (Algebra.leftMulMatrix (Module.finBasis K L) x)
  map_zero' := by rw [map_zero, spectralRadiusLim_zero]
  add_le' x y := by grw [map_add, ((Commute.all x y).map _).spectralRadiusLim_add_le]
  neg' x := by rw [map_neg, spectralRadiusLim_neg]
  mul_le' x y := by grw [map_mul, ((Commute.all x y).map _).spectralRadiusLim_mul_le]
  eq_zero_of_map_eq_zero' x h := by
    have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
    have : Commute x x⁻¹ := by simp -- merge master
    have hx := (this.map (Algebra.leftMulMatrix (Module.finBasis K L))).spectralRadiusLim_mul_le
    contrapose! hx
    simp [← map_mul, h, hx]
  smul' x y := by rw [map_smul, spectralRadiusLim_smul]

variable {K L M}

theorem spectralRadiusLimNorm_def (x : L) : spectralRadiusLimNorm K L x =
    spectralRadiusLim (Algebra.leftMulMatrix (Module.finBasis K L) x) :=
  rfl

@[simp]
theorem spectralRadiusLimNorm_one : spectralRadiusLimNorm K L 1 = 1 := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  rw [spectralRadiusLimNorm_def, map_one, spectralRadiusLim_one]

theorem spectralRadiusLimNorm_extends (x : K) :
    spectralRadiusLimNorm K L (algebraMap K L x) = ‖x‖ := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, spectralRadiusLimNorm_one, mul_one]

theorem isPowMul_spectralRadiusLimNorm : IsPowMul (spectralRadiusLimNorm K L) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  intro x k hk
  simp_rw [spectralRadiusLimNorm_def, map_pow, spectralRadiusLim_pow]

theorem spectralRadiusLimNorm_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (x : L) :
    spectralRadiusLimNorm K L x = spectralRadiusLim (Algebra.leftMulMatrix b x) := by
  let ι' := Fin (Module.finrank K L)
  let b' := Module.finBasis K L
  rw [spectralRadiusLimNorm_def]
  let m : Matrix ι ι K := Algebra.leftMulMatrix b x
  let m' : Matrix ι' ι' K := Algebra.leftMulMatrix b' x
  change spectralRadiusLim m' = spectralRadiusLim m
  let v := b.toMatrix b'
  let v' := b'.toMatrix b
  have h : v * m' * v' = m := by
    apply basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
  have h' : v' * m * v = m' := by
    apply basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
  rw [← h']
  exact Matrix.spectralRadiusLim_conj v' m v (b'.toMatrix_mul_toMatrix_flip b)
    (b.toMatrix_mul_toMatrix_flip b')

theorem spectralRadiusLimNorm_algebraMap (x : L) :
    spectralRadiusLimNorm K M (algebraMap L M x) = spectralRadiusLimNorm K L x := by
  have : FiniteDimensional L M := .of_restrictScalars_finite K L M
  have : NeZero (Module.finrank L M) := ⟨Module.finrank_pos.ne'⟩
  let bKL := Module.finBasis K L
  let bLM := Module.finBasis L M
  rw [spectralRadiusLimNorm_apply bKL, spectralRadiusLimNorm_apply (bKL.smulTower bLM),
    Algebra.smulTower_leftMulMatrix_algebraMap, Matrix.spectralRadiusLim_blockMatrix]

end spectralRadiusLimNorm

section spectralNorm

open Filter

open scoped Topology

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

open Classical in
/-- This will eventually replace `spectralNorm`. -/
noncomputable def spectralNorm' (x : L) : ℝ :=
  if hx : IsAlgebraic K x then
    haveI := adjoin.finiteDimensional hx.isIntegral
    spectralRadiusLimNorm K K⟮x⟯ (AdjoinSimple.gen K x)
  else 0

variable {K L}

theorem spectralNorm'_eq_zero {x : L} (hx : ¬ IsAlgebraic K x) : spectralNorm' K L x = 0 :=
  dite_eq_right hx

theorem IsAlgebraic.spectralNorm'_eq {x : L} (hx : IsAlgebraic K x) :
    haveI := adjoin.finiteDimensional hx.isIntegral
    spectralNorm' K L x = spectralRadiusLimNorm K K⟮x⟯ (AdjoinSimple.gen K x) :=
  dite_eq_left hx

theorem FiniteDimensional.spectralNorm'_eq [FiniteDimensional K L] (x : L) :
    spectralNorm' K L x = spectralRadiusLimNorm K L x :=
  (Algebra.IsAlgebraic.isAlgebraic x).spectralNorm'_eq.trans
    (spectralRadiusLimNorm_algebraMap (AdjoinSimple.gen K x)).symm

theorem spectralNorm'_algebraMap {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm' K L (algebraMap E L x) = spectralNorm' K E x := by
  by_cases hx : IsAlgebraic K x
  · rw [hx.spectralNorm'_eq, hx.algebraMap.spectralNorm'_eq]
    let f := IsScalarTower.toAlgHom K E L
    have hf : K⟮x⟯.map f = K⟮algebraMap E L x⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IsScalarTower.toAlgHom_apply]
    let g : K⟮x⟯ →ₐ[K] K⟮algebraMap E L x⟯ := (equivMap K⟮x⟯ f).trans (equivOfEq hf)
    let := g.toRingHom.toAlgebra
    have := adjoin.finiteDimensional hx.isIntegral
    have : FiniteDimensional K K⟮algebraMap E L x⟯ :=
      adjoin.finiteDimensional hx.algebraMap.isIntegral
    exact spectralRadiusLimNorm_algebraMap (AdjoinSimple.gen K x)
  · rw [spectralNorm'_eq_zero hx, spectralNorm'_eq_zero]
    exact mt (isAlgebraic_algebraMap_iff (algebraMap E L).injective).mp hx

theorem spectralNorm'_eq_of_mem (E : IntermediateField K L) [FiniteDimensional K E]
    (x : L) (y : E) (h : x = y) : spectralNorm' K L x = spectralRadiusLimNorm K E y := by
  rw [h, ← E.algebraMap_apply, spectralNorm'_algebraMap, FiniteDimensional.spectralNorm'_eq]

@[simp]
theorem spectralNorm'_zero : spectralNorm' K L 0 = 0 := by
  rw [spectralNorm'_eq_of_mem ⊥ 0 0 rfl, map_zero]

@[simp]
theorem spectralNorm'_one : spectralNorm' K L 1 = 1 := by
  rw [spectralNorm'_eq_of_mem ⊥ 1 1 rfl, spectralRadiusLimNorm_one]

theorem spectralNorm'_neg (x : L) : spectralNorm' K L (-x) = spectralNorm' K L x := by
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [spectralNorm'_eq_of_mem K⟮x⟯ x (AdjoinSimple.gen K x) rfl,
      spectralNorm'_eq_of_mem K⟮x⟯ (-x) (-AdjoinSimple.gen K x) rfl, map_neg_eq_map]
  · rw [spectralNorm'_eq_zero, spectralNorm'_eq_zero hx]
    contrapose! hx
    simpa using hx.neg

theorem spectralNorm'_smul (x : K) (y : L) :
    spectralNorm' K L (x • y) = ‖x‖ * spectralNorm' K L y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : IsAlgebraic K y
  · have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional hy.isIntegral
    rw [spectralNorm'_eq_of_mem K⟮y⟯ y (AdjoinSimple.gen K y) rfl,
      spectralNorm'_eq_of_mem K⟮y⟯ (x • y) (x • AdjoinSimple.gen K y) rfl, map_smul_eq_mul]
  · rw [spectralNorm'_eq_zero, spectralNorm'_eq_zero hy, mul_zero]
    contrapose! hy
    simpa [hx] using hy.smul x⁻¹

theorem spectralNorm'_extends (x : K) : spectralNorm' K L (algebraMap K L x) = ‖x‖ := by
  rw [Algebra.algebraMap_eq_smul_one, spectralNorm'_smul, spectralNorm'_one, mul_one]

theorem spectralNorm'_add {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm' K L (x + y) ≤ spectralNorm' K L x + spectralNorm' K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [spectralNorm'_eq_of_mem K⟮x, y⟯ x (AdjoinPair.gen₁ K x y) rfl,
    spectralNorm'_eq_of_mem K⟮x, y⟯ y (AdjoinPair.gen₂ K x y) rfl,
    spectralNorm'_eq_of_mem K⟮x, y⟯ (x + y) (AdjoinPair.gen₁ K x y + AdjoinPair.gen₂ K x y) rfl]
  apply map_add_le_add

theorem spectralNorm'_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm' K L (x * y) ≤ spectralNorm' K L x * spectralNorm' K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [spectralNorm'_eq_of_mem K⟮x, y⟯ x (AdjoinPair.gen₁ K x y) rfl,
    spectralNorm'_eq_of_mem K⟮x, y⟯ y (AdjoinPair.gen₂ K x y) rfl,
    spectralNorm'_eq_of_mem K⟮x, y⟯ (x * y) (AdjoinPair.gen₁ K x y * AdjoinPair.gen₂ K x y) rfl]
  apply map_mul_le_mul

theorem eq_zero_of_spectralNorm'_eq_zero {x : L} (hx : IsAlgebraic K x)
    (hx0 : spectralNorm' K L x = 0) : x = 0 := by
  rw [hx.spectralNorm'_eq] at hx0
  exact Subtype.ext_iff.mp (eq_zero_of_map_eq_zero _ hx0)

variable (K L) in
theorem isPowMul_spectralNorm' : IsPowMul (spectralNorm' K L) := by
  intro x k hk
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [spectralNorm'_eq_of_mem K⟮x⟯ x (AdjoinSimple.gen K x) rfl,
      spectralNorm'_eq_of_mem K⟮x⟯ (x ^ k) (AdjoinSimple.gen K x ^ k) rfl,
      isPowMul_spectralRadiusLimNorm (AdjoinSimple.gen K x) hk]
  · rw [spectralNorm'_eq_zero hx, spectralNorm'_eq_zero, zero_pow (by grind)]
    contrapose! hx
    exact hx.of_pow hk

end spectralNorm

section spectralAlgNorm

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

open Algebra.IsAlgebraic in
noncomputable def spectralAlgNorm' : AlgebraNorm K L where
  toFun := spectralNorm' K L
  map_zero' := spectralNorm'_zero
  add_le' x y := spectralNorm'_add (isAlgebraic x) (isAlgebraic y)
  neg' := spectralNorm'_neg
  mul_le' x y := spectralNorm'_mul (isAlgebraic x) (isAlgebraic y)
  eq_zero_of_map_eq_zero' x := eq_zero_of_spectralNorm'_eq_zero (isAlgebraic x)
  smul' := spectralNorm'_smul

variable {K L}

theorem spectralAlgNorm'_def (x : L) : spectralAlgNorm' K L x = spectralNorm' K L x :=
  rfl

theorem spectralAlgNorm'_extends (x : K) : spectralAlgNorm' K L (algebraMap K L x) = ‖x‖ :=
  spectralNorm'_extends x

theorem spectralAlgNorm'_one : spectralAlgNorm' K L (1 : L) = 1 :=
  spectralNorm'_one

theorem isPowMul_spectralAlgNorm' : IsPowMul (spectralAlgNorm' K L) :=
  isPowMul_spectralNorm' K L

variable (K L) in
/-- The spectral norm is a multiplicative `K`-algebra norm on `L`. -/
noncomputable def spectralMulAlgNorm' [CompleteSpace K] : MulAlgebraNorm K L :=
  (spectralAlgNorm' K L).toMulAlgebraNorm isPowMul_spectralAlgNorm'

variable (K L) in
/-- The spectral norm is an absolute value on `L`. -/
noncomputable def spectralAbsoluteValue' [CompleteSpace K] : AbsoluteValue L ℝ :=
  (spectralMulAlgNorm' K L).toAbsoluteValue

end spectralAlgNorm

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [CompleteSpace (WithAbs v)]

/-- The unique extension of a complete absolue value to a finite extension. -/
noncomputable def extension : AbsoluteValue L ℝ :=
  spectralAbsoluteValue' (WithAbs v) L

theorem extension_def : v.extension L = (spectralMulAlgNorm' (WithAbs v) L).toAbsoluteValue :=
  rfl

instance : (v.extension L).LiesOver v where
  comp_eq := by
    ext x
    change v.extension L (algebraMap K L x) = _ -- lemma for `LiesOver`
    rw [IsScalarTower.algebraMap_apply K (WithAbs v) L, WithAbs.algebraMap_right_apply]
    simp [extension_def, Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, WithAbs.norm_toAbs_eq]

end AbsoluteValue

section

theorem NormedAlgebra.norm_eq_spectralNorm' (K : Type*) [NormedField K] {L : Type*}
    [CompleteSpace K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ = spectralNorm' K L x :=
  MulAlgebraNorm.ext_iff.mp ((toMulAlgebraNorm K L).unique (spectralMulAlgNorm' K L)) x

theorem spectralNorm'_eq_of_equiv {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : L) : spectralNorm' K L x = spectralNorm' K L (σ x) := by
  sorry

@[instance_reducible]
noncomputable def spectralNorm'.normedField (K L : Type*) [NormedField K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [CompleteSpace K] : NormedField L :=
  (spectralAbsoluteValue' K L).toNormedField

@[instance_reducible]
noncomputable def spectralNorm'.nontriviallyNormedField (K L : Type*) [NontriviallyNormedField K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [CompleteSpace K] : NontriviallyNormedField L where
  __ := spectralNorm'.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq (spectralNorm'_extends x).symm⟩

@[instance_reducible]
noncomputable def spectralNorm'.normedAlgebra
    (K L : Type*) [NormedField K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [CompleteSpace K] :
    letI := spectralNorm'.normedField K L
    NormedAlgebra K L where
  __ := spectralNorm'.normedField K L
  norm_smul_le x y := ((spectralAlgNorm' K L).smul' x y).le

@[instance_reducible]
noncomputable def spectralNorm'.normedAlgebra' (K E L : Type*) [NormedField K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [NormedField E]
    [NormedAlgebra K E] [Algebra E L] [IsScalarTower K E L] :
    letI := spectralNorm'.normedField K L
    NormedAlgebra E L where
  __ := spectralNorm'.normedField K L
  norm_smul_le _ _ := by
    let := spectralNorm'.normedAlgebra K L
    have := Algebra.IsAlgebraic.tower_bot K E L
    apply le_of_eq
    simp [Algebra.smul_def]
    simp [NormedAlgebra.norm_eq_spectralNorm' K, spectralNorm'_algebraMap]

theorem isNonarchimedean_spectralNorm' {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    [IsUltrametricDist K] [Algebra.IsAlgebraic K L] : IsNonarchimedean (spectralNorm' K L) := by
  rw [IsNonarchimedean]
  intro x y
  sorry

end
