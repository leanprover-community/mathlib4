/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Unbundled.GelfandRadiusNorm
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique

/-!
# Spectral norms and extensions of absolute values

This file defines spectral norms and uses them to construct extensions of absolute values.
-/

@[expose] public section

-- todo: golf `normFromConst` file

section spectralNorm

open Filter

open scoped Topology

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

open Classical in
/-- This will eventually replace `spectralNorm`. -/
noncomputable def spectralNorm (x : L) : ℝ :=
  if hx : IsAlgebraic K x then
    haveI := adjoin.finiteDimensional hx.isIntegral
    gelfandRadiusNorm K K⟮x⟯ (AdjoinSimple.gen K x)
  else 0

variable {K L}

theorem spectralNorm_eq_zero {x : L} (hx : ¬ IsAlgebraic K x) : spectralNorm K L x = 0 :=
  dite_eq_right hx

theorem IsAlgebraic.spectralNorm_eq {x : L} (hx : IsAlgebraic K x) :
    haveI := adjoin.finiteDimensional hx.isIntegral
    spectralNorm K L x = gelfandRadiusNorm K K⟮x⟯ (AdjoinSimple.gen K x) :=
  dite_eq_left hx

theorem FiniteDimensional.spectralNorm_eq [FiniteDimensional K L] (x : L) :
    spectralNorm K L x = gelfandRadiusNorm K L x :=
  (Algebra.IsAlgebraic.isAlgebraic x).spectralNorm_eq.trans
    (gelfandRadiusNorm_algebraMap K L (AdjoinSimple.gen K x)).symm

@[simp]
theorem spectralNorm_algebraMap {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm K L (algebraMap E L x) = spectralNorm K E x := by
  by_cases hx : IsAlgebraic K x
  · rw [hx.spectralNorm_eq, hx.algebraMap.spectralNorm_eq]
    let f := IsScalarTower.toAlgHom K E L
    have hf : K⟮x⟯.map f = K⟮algebraMap E L x⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IsScalarTower.toAlgHom_apply]
    let g : K⟮x⟯ →ₐ[K] K⟮algebraMap E L x⟯ := (equivMap K⟮x⟯ f).trans (equivOfEq hf)
    let := g.toRingHom.toAlgebra
    have := adjoin.finiteDimensional hx.isIntegral
    have : FiniteDimensional K K⟮algebraMap E L x⟯ :=
      adjoin.finiteDimensional hx.algebraMap.isIntegral
    exact gelfandRadiusNorm_algebraMap K (K⟮algebraMap E L x⟯) (AdjoinSimple.gen K x)
  · rw [spectralNorm_eq_zero hx, spectralNorm_eq_zero]
    exact mt (isAlgebraic_algebraMap_iff (algebraMap E L).injective).mp hx

theorem IntermediateField.spectralNorm_eq (E : IntermediateField K L) [FiniteDimensional K E]
    (x : L) (y : E) (h : x = y) : spectralNorm K L x = gelfandRadiusNorm K E y := by
  rw [h, ← E.algebraMap_apply, spectralNorm_algebraMap, FiniteDimensional.spectralNorm_eq]

@[simp]
theorem spectralNorm_zero : spectralNorm K L 0 = 0 := by
  rw [IntermediateField.spectralNorm_eq ⊥ 0 0 rfl, map_zero]

@[simp]
theorem spectralNorm_one : spectralNorm K L 1 = 1 := by
  rw [IntermediateField.spectralNorm_eq ⊥ 1 1 rfl, gelfandRadiusNorm_one]

theorem spectralNorm_neg (x : L) : spectralNorm K L (-x) = spectralNorm K L x := by
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [K⟮x⟯.spectralNorm_eq x (AdjoinSimple.gen K x) rfl,
      K⟮x⟯.spectralNorm_eq (-x) (-AdjoinSimple.gen K x) rfl, map_neg_eq_map]
  · rw [spectralNorm_eq_zero, spectralNorm_eq_zero hx]
    contrapose hx
    simpa using hx.neg

theorem spectralNorm_smul (x : K) (y : L) :
    spectralNorm K L (x • y) = ‖x‖ * spectralNorm K L y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : IsAlgebraic K y
  · have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional hy.isIntegral
    rw [K⟮y⟯.spectralNorm_eq y (AdjoinSimple.gen K y) rfl,
      K⟮y⟯.spectralNorm_eq (x • y) (x • AdjoinSimple.gen K y) rfl, map_smul_eq_mul]
  · rw [spectralNorm_eq_zero, spectralNorm_eq_zero hy, mul_zero]
    contrapose hy
    simpa [hx] using hy.smul x⁻¹

theorem spectralNorm_eq_norm (x : K) : spectralNorm K K x = ‖x‖ := by
  simpa using spectralNorm_smul x (1 : K)

theorem spectralNorm_add {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x + y) ≤ spectralNorm K L x + spectralNorm K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [K⟮x, y⟯.spectralNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq (x + y) (AdjoinPair.gen₁ K x y + AdjoinPair.gen₂ K x y) rfl]
  apply map_add_le_add

theorem spectralNorm_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) ≤ spectralNorm K L x * spectralNorm K L y := by
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  rw [K⟮x, y⟯.spectralNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq (x * y) (AdjoinPair.gen₁ K x y * AdjoinPair.gen₂ K x y) rfl]
  apply map_mul_le_mul

theorem eq_zero_of_spectralNorm_eq_zero {x : L} (hx : IsAlgebraic K x)
    (hx0 : spectralNorm K L x = 0) : x = 0 := by
  rw [hx.spectralNorm_eq] at hx0
  exact Subtype.ext_iff.mp (eq_zero_of_map_eq_zero _ hx0)

variable (K L) in
theorem isPowMul_spectralNorm : IsPowMul (spectralNorm K L) := by
  intro x k hk
  by_cases hx : IsAlgebraic K x
  · have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
    rw [K⟮x⟯.spectralNorm_eq x (AdjoinSimple.gen K x) rfl,
      K⟮x⟯.spectralNorm_eq (x ^ k) (AdjoinSimple.gen K x ^ k) rfl,
      isPowMul_gelfandRadiusNorm K K⟮x⟯ (AdjoinSimple.gen K x) hk]
  · rw [spectralNorm_eq_zero hx, spectralNorm_eq_zero, zero_pow (by grind)]
    contrapose hx
    exact hx.of_pow hk

end spectralNorm

section spectralAlgNorm

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

open Algebra.IsAlgebraic in
/-- The spectral norm is a `K`-algebra norm on `L`. -/
noncomputable def spectralAlgNorm : AlgebraNorm K L where
  toFun := spectralNorm K L
  map_zero' := spectralNorm_zero
  add_le' x y := spectralNorm_add (isAlgebraic x) (isAlgebraic y)
  neg' := spectralNorm_neg
  mul_le' x y := spectralNorm_mul (isAlgebraic x) (isAlgebraic y)
  eq_zero_of_map_eq_zero' x := eq_zero_of_spectralNorm_eq_zero (isAlgebraic x)
  smul' := spectralNorm_smul

variable {K L}

theorem spectralAlgNorm_def (x : L) : spectralAlgNorm K L x = spectralNorm K L x :=
  rfl

@[simp]
theorem spectralAlgNorm_algebraMap {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_bot K E L
    spectralAlgNorm K L (algebraMap E L x) = spectralAlgNorm K E x :=
  spectralNorm_algebraMap x

@[simp]
theorem spectralAlgNorm_one : spectralAlgNorm K L (1 : L) = 1 :=
  spectralNorm_one

@[simp]
theorem spectralAlgNorm_eq_norm (x : K) : spectralAlgNorm K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (spectralAlgNorm K K) x 1

theorem isPowMul_spectralAlgNorm : IsPowMul (spectralAlgNorm K L) :=
  isPowMul_spectralNorm K L

variable (K L) in
/-- The spectral norm is a multiplicative `K`-algebra norm on `L`. -/
noncomputable def spectralMulAlgNorm [CompleteSpace K] : MulAlgebraNorm K L :=
  (spectralAlgNorm K L).toMulAlgebraNorm isPowMul_spectralAlgNorm

variable (K L) in
/-- The spectral norm is an absolute value on `L`. -/
noncomputable def spectralAbsoluteValue [CompleteSpace K] : AbsoluteValue L ℝ :=
  (spectralMulAlgNorm K L).toAbsoluteValue

end spectralAlgNorm

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [CompleteSpace (WithAbs v)]

/-- The unique extension of a complete absolute value to a finite extension. -/
noncomputable def extension : AbsoluteValue L ℝ :=
  spectralAbsoluteValue (WithAbs v) L

theorem extension_def : v.extension L = (spectralMulAlgNorm (WithAbs v) L).toAbsoluteValue :=
  rfl

instance : (v.extension L).LiesOver v where
  under_eq := by
    ext x
    change v.extension L (algebraMap K L x) = _ -- lemma for `LiesOver`
    rw [IsScalarTower.algebraMap_apply K (WithAbs v) L, WithAbs.algebraMap_right_apply]
    simp [extension_def, Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, WithAbs.norm_toAbs_eq]

end AbsoluteValue

section

theorem NormedAlgebra.norm_eq_spectralNorm (K : Type*) [NormedField K] {L : Type*}
    [CompleteSpace K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ = spectralNorm K L x :=
  MulAlgebraNorm.ext_iff.mp ((toMulAlgebraNorm K L).unique (spectralMulAlgNorm K L)) x

@[simp]
theorem spectralNorm_algHom {K L M F : Type*} [NormedField K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FunLike F L M] [AlgHomClass F K L M] (σ : F) (x : L) :
    spectralNorm K M (σ x) = spectralNorm K L x :=
  let := (AlgHom.ofClass σ).toAlgebra
  spectralNorm_algebraMap x

/-- The spectral norm gives `L` the structure of a normed field. -/
@[instance_reducible]
noncomputable def spectralNorm.normedField (K L : Type*) [NormedField K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [CompleteSpace K] : NormedField L :=
  (spectralAbsoluteValue K L).toNormedField

/-- The spectral norm gives `L` the structure of a normed algebra. -/
@[instance_reducible]
noncomputable def spectralNorm.normedAlgebra
    (K L : Type*) [NormedField K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [CompleteSpace K] :
    letI := spectralNorm.normedField K L
    NormedAlgebra K L where
  __ := spectralNorm.normedField K L
  norm_smul_le x y := ((spectralAlgNorm K L).smul' x y).le

/-- The spectral norm gives `L` the structure of a nontrivally normed field. -/
@[instance_reducible]
noncomputable def spectralNorm.nontriviallyNormedField (K L : Type*) [NontriviallyNormedField K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [CompleteSpace K] :
    NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial := by
    let := spectralNorm.normedAlgebra K L
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    use algebraMap K L x
    rwa [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm_algebraMap, spectralNorm_eq_norm]

/-- The spectral norm gives `L` the structure of a normed algebra over any intermediate field. -/
@[instance_reducible]
noncomputable def spectralNorm.normedAlgebra' (K E L : Type*) [NormedField K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [NormedField E]
    [NormedAlgebra K E] [Algebra E L] [IsScalarTower K E L] :
    letI := spectralNorm.normedField K L
    NormedAlgebra E L where
  __ := spectralNorm.normedField K L
  norm_smul_le _ _ := by
    let := spectralNorm.normedAlgebra K L
    have := Algebra.IsAlgebraic.tower_bot K E L
    apply le_of_eq
    simp [Algebra.smul_def]
    simp [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm_algebraMap]

open IntermediateField in
theorem isNonarchimedean_spectralNorm {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    [IsUltrametricDist K] [Algebra.IsAlgebraic K L] : IsNonarchimedean (spectralNorm K L) := by
  rw [IsNonarchimedean]
  intro x y
  have : FiniteDimensional K K⟮x, y⟯ := finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral x) (Algebra.IsIntegral.isIntegral y)
  rw [K⟮x, y⟯.spectralNorm_eq x (AdjoinPair.gen₁ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq y (AdjoinPair.gen₂ K x y) rfl,
    K⟮x, y⟯.spectralNorm_eq (x + y) (AdjoinPair.gen₁ K x y + AdjoinPair.gen₂ K x y) rfl]
  apply isNonarchimedean_gelfandRadiusNorm

end
