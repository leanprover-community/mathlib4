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
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral norms and extensions of absolute values

This file defines spectral norms and uses them to construct extensions of absolute values.

For a normed algebra `A` with `‖1‖ = 1` over a normed field `𝕜`, the spectral radius limit
`lim ‖x ^ k‖ ^ (1 / k)` defines a function `f : A → ℝ` satisfying the following properties:
* `f 0 = 0` (`spectralRadiusLim_zero`),
* `f 1 = 1` (`spectralRadiusLim_one`),
* `0 ≤ f x` for all `x : A` (`spectralRadiusLim_zero`),
* `f (x + y) ≤ f x + f y` for all commuting `x y : A` (`Commute.spectralRadiusLim_add_le`),
* `f (x * y) ≤ f x * f y` for all commuting `x y : A` (`Commute.spectralRadiusLim_mul_le`),
* `f (x ^ k) = (f x) ^ k` for all `x : A` and `k : ℕ` (`spectralRadiusLim_pow`),
* `f (c • x) = ‖c‖ * f x` for all `c : 𝕜` and `x : A` (`spectralRadiusLim_smul`).

In general, if `A` is an algebra over a normed field `𝕜`, then a function `f : A → ℝ` satisfying
these properties is called a **spectral norm**.

For a finite-dimensional algebra over a complete normed field, there exists a unique spectral norm
(see `spectralNorm` and `spectralNorm_unique`).

For a finite extension of a complete normed field, applying uniqueness to the spectral norm `‖x‖`
and the modified spectral norm `‖x‖_y = lim_{n → ∞} ‖x * y ^ n‖ / ‖y‖ ^ n` proves that the
spectral norm is multiplicative, defining an absolute value (see `SpectralNorm.absoluteValue`).

This gives a construction of extensions of absolute values that works uniformly across the
archimedean and non-archimedean cases (bypassing Gelfand-Mazur).

This file follows a [MathOverflow answer](https://mathoverflow.net/a/419366/95685) by Denis Nardin.

## Main definitions

* `SpectralNorm 𝕜 A`: the type of all spectral norms on `A` over `𝕜`.
* `spectralRadiusLimNorm`: spectral norm defined by the spectral radius limit.
* `spectralNorm`: a choice of spectral norm on a finite-dimensional algebra over a normed field.
* `SpectralNorm.absoluteValue`: the absolute value on a finite extension of a complete normed field.

## Main statements

* `spectralNorm_unique`: uniqueness of spectral norms on a finite-dimensional algebra over a
  complete normed field.
-/

@[expose] public section

open Filter Topology in
theorem tendsto_nhds_unique_of_forall {X Y : Type*} [TopologicalSpace X] [T2Space X] {f g : Y → X}
    {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b))
    (hfg : ∀ y, f y = g y) : a = b :=
  tendsto_nhds_unique_of_eventuallyEq ha hb (Eventually.of_forall hfg)

section matrices

open scoped Matrix.Norms.Operator

theorem Matrix.linfty_opNNNorm_blockDiagonal
    {R m n o : Type*} [SeminormedAddCommGroup R]
    [DecidableEq o] [Fintype m] [Fintype n] [Fintype o] (M : o → Matrix m n R) :
    ‖blockDiagonal M‖₊ = ‖M‖₊ := by
  simp_rw [Pi.nnnorm_def, linfty_opNNNorm_def, ← Finset.univ_product_univ,
    Finset.sup_product_right, Finset.sum_product, blockDiagonal_apply, apply_ite]
  simp

theorem Matrix.linfty_opNorm_blockDiagonal
    {R m n o : Type*} [SeminormedAddCommGroup R]
    [DecidableEq o] [Fintype m] [Fintype n] [Fintype o] (M : o → Matrix m n R) :
    ‖blockDiagonal M‖ = ‖M‖ :=
  congr_arg ((↑) : NNReal → Real) <| linfty_opNNNorm_blockDiagonal M

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

theorem Matrix.spectralRadiusLim_conj {R m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [NormedCommRing R]
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hAC : A * C = 1) (hCA : C * A = 1) : spectralRadiusLim (A * B * C) = spectralRadiusLim B := by
  refine le_antisymm (Matrix.spectralRadiusLim_conj_le A B C hAC hCA) ?_
  have h : C * (A * B * C) * A = B := by
    transitivity (C * A) * B * (C * A) <;> grind [Matrix.mul_assoc]
  have := Matrix.spectralRadiusLim_conj_le C (A * B * C) A hCA hAC
  rwa [h] at this

theorem Matrix.spectralRadiusLim_blockMatrix {R m : Type*} [DecidableEq m] [Fintype m]
    [NormedCommRing R] (A : Matrix m m R) (n : Type*) [DecidableEq n] [Fintype n] [Nonempty n] :
    spectralRadiusLim (Matrix.blockDiagonal fun _ : n ↦ A) = spectralRadiusLim A := by
  refine tendsto_nhds_unique_of_forall (tendsto_spectralRadiusLim (blockDiagonal fun _ ↦ A))
    (tendsto_spectralRadiusLim A) fun k ↦ ?_
  rw [← blockDiagonal_pow, Matrix.linfty_opNorm_blockDiagonal, Pi.pow_def, pi_norm_const]

end matrices

section unique

open IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Type synonym of `K⟮x⟯`. -/
private def AlgebraNorm.copy (_f : AlgebraNorm K L) (x : L) : Type _ := K⟮x⟯
deriving Field, Algebra K

private instance (f : AlgebraNorm K L) (x : L) : FiniteDimensional K (f.copy x) :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)

private instance (f : AlgebraNorm K L) (x : L) : Algebra (f.copy x) L :=
  inferInstanceAs (Algebra K⟮x⟯ L)

/-- The ring norm defined by a spectral norm. -/
private def AlgebraNorm.ringNorm (f : AlgebraNorm K L) (x : L) : RingNorm (f.copy x) where
  toFun y := f ((algebraMap (f.copy x) L) y)
  map_zero' := map_zero _
  add_le' a b := map_add_le_add _ _ _
  neg' y := by simp
  mul_le' a b := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' a ha := by rwa [map_eq_zero_iff_eq_zero, map_eq_zero] at ha

private instance (f : AlgebraNorm K L) (x : L) : NormedRing (f.copy x) :=
  (f.ringNorm x).toNormedRing

private instance (f : AlgebraNorm K L) (x : L) : NormedAlgebra K (f.copy x) where
  norm_smul_le c y := (map_smul_eq_mul f c (algebraMap (f.copy x) L y)).le

theorem IsPowMul.unique [CompleteSpace K] {f g : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hg_pm : IsPowMul g) : f = g := by
  apply eq_of_powMul_faithful f hf_pm g hg_pm
  intro x
  let T₀ : g.copy x ≃ₗ[K] f.copy x := LinearEquiv.refl K K⟮x⟯
  let T : g.copy x ≃L[K] f.copy x := T₀.toContinuousLinearEquiv
  obtain ⟨C1, hC1_pos, hC1⟩ := T.symm.toContinuousLinearMap.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ := T.toContinuousLinearMap.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

end unique

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

@[simp]
theorem spectralRadiusLimNorm_def (x : L) : spectralRadiusLimNorm K L x =
    spectralRadiusLim (Algebra.leftMulMatrix (Module.finBasis K L) x) :=
  rfl

theorem isPowMul_spectralRadiusLimNorm : IsPowMul (spectralRadiusLimNorm K L) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  intro x k hk
  simp_rw [spectralRadiusLimNorm_def, map_pow, spectralRadiusLim_pow]

variable {K L} in
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

section new

open Filter

open scoped Topology

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

open Classical in
noncomputable def spectralNorm (x : L) : ℝ :=
  if hx : IsIntegral K x then
    haveI := adjoin.finiteDimensional hx
    spectralRadiusLimNorm K K⟮x⟯ (AdjoinSimple.gen K x)
  else 0

def spectralAlgNorm [Algebra.IsAlgebraic K L] : AlgebraNorm K L := by
  -- use `spectralNorm`
  sorry

end new

open Filter

open scoped Topology

variable {𝕜 A B : Type*}

section Ring

variable [SeminormedCommRing 𝕜] [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]

variable (𝕜 A) in
/-- The type of all spectral norms on `A` over `𝕜`. -/
@[ext]
structure SpectralNorm extends OneHom A ℝ, ZeroHom A ℝ where
  nonneg' x : 0 ≤ toFun x
  map_add_le_add' x y (h : Commute x y) : toFun (x + y) ≤ toFun x + toFun y
  map_mul_le_mul' x y (h : Commute x y) : toFun (x * y) ≤ toFun x * toFun y
  map_pow' x k : toFun (x ^ k) = toFun x ^ k
  map_smul_eq_mul' (c : 𝕜) x : toFun (c • x) = ‖c‖ * toFun x

namespace SpectralNorm

instance : FunLike (SpectralNorm 𝕜 A) A ℝ where
  coe f := f.toFun
  coe_injective _ _ := SpectralNorm.ext

@[simp]
theorem coe_toZeroHom (f : SpectralNorm 𝕜 A) : ⇑f.toZeroHom = f := rfl

@[simp]
theorem coe_toOneHom (f : SpectralNorm 𝕜 A) : ⇑f.toOneHom = f := rfl

instance : ZeroHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_zero f := f.map_zero'

instance : OneHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_one f := f.map_one'

instance : NonnegHomClass (SpectralNorm 𝕜 A) A ℝ where
  apply_nonneg := nonneg'

protected theorem map_add_le_add (f : SpectralNorm 𝕜 A) {x y : A} (h : Commute x y) :
    f (x + y) ≤ f x + f y :=
  f.map_add_le_add' x y h

protected theorem map_mul_le_mul (f : SpectralNorm 𝕜 A) {x y : A} (h : Commute x y) :
    f (x * y) ≤ f x * f y :=
  f.map_mul_le_mul' x y h

@[simp]
protected theorem map_pow (f : SpectralNorm 𝕜 A) (x : A) (k : ℕ) : f (x ^ k) = f x ^ k :=
  f.map_pow' x k

protected theorem map_smul_eq_mul (f : SpectralNorm 𝕜 A) (c : 𝕜) (x : A) : f (c • x) = ‖c‖ * f x :=
  f.map_smul_eq_mul' c x

/-- The pullback of a spectral norm along an algebra homomorphism. -/
protected def comap (f : SpectralNorm 𝕜 B) (g : A →ₐ[𝕜] B) : SpectralNorm 𝕜 A where
  toFun x := f (g x)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  nonneg' x := apply_nonneg f (g x)
  map_add_le_add' x y h := by grw [map_add, f.map_add_le_add (h.map g)]
  map_mul_le_mul' x y h := by grw [map_mul, f.map_mul_le_mul (h.map g)]
  map_pow' x k := by rw [map_pow, f.map_pow]
  map_smul_eq_mul' c x := by rw [map_smul, f.map_smul_eq_mul]

end SpectralNorm

end Ring

section CommRing

variable [SeminormedCommRing 𝕜] [CommRing A] [Algebra 𝕜 A]

instance : SubadditiveHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_add_le_add f x y := f.map_add_le_add (Commute.all x y)

instance : SubmultiplicativeHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_mul_le_mul f x y := f.map_mul_le_mul (Commute.all x y)

instance [NormOneClass 𝕜] : SeminormClass (SpectralNorm 𝕜 A) 𝕜 A where
  map_zero f := map_zero f
  map_neg_eq_map f x := by simpa using f.map_smul_eq_mul (-1) x
  map_smul_eq_mul f := f.map_smul_eq_mul

instance [NormOneClass 𝕜] : RingSeminormClass (SpectralNorm 𝕜 A) A ℝ where

end CommRing

@[simp]
protected theorem SpectralNorm.eq_zero_iff [SeminormedCommRing 𝕜] [DivisionRing A] [Algebra 𝕜 A]
    {f : SpectralNorm 𝕜 A} {x : A} : f x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : Commute x x⁻¹ := Commute.inv_right₀ rfl -- todo: library lemma
    have h := f.map_mul_le_mul this
    contrapose! h
    simp [h, hx]
  · rw [hx, map_zero]

instance [SeminormedCommRing 𝕜] [NormOneClass 𝕜] [Field A] [Algebra 𝕜 A] :
    RingNormClass (SpectralNorm 𝕜 A) A ℝ where
  eq_zero_of_map_eq_zero f := f.eq_zero_iff.mp

variable (𝕜 A) in
/-- The spectral norm defined by the spectral radius limit `lim ‖x ^ k‖ ^ (1 / k)`. -/
noncomputable def spectralRadiusLimNorm [NormedField 𝕜] [SeminormedRing A] [NormOneClass A]
    [NormedAlgebra 𝕜 A] : SpectralNorm 𝕜 A where
  toFun := spectralRadiusLim
  map_zero' := spectralRadiusLim_zero
  map_one' := spectralRadiusLim_one
  nonneg' := spectralRadiusLim_nonneg
  map_add_le_add' _ _ := Commute.spectralRadiusLim_add_le
  map_mul_le_mul' _ _ := Commute.spectralRadiusLim_mul_le
  map_pow' := spectralRadiusLim_pow
  map_smul_eq_mul' := spectralRadiusLim_smul

section NormedField

variable [NormedField 𝕜] [Field A] [Algebra 𝕜 A] [FiniteDimensional 𝕜 A]

variable (𝕜 A) in
open scoped Matrix.Norms.Operator in
/-- A choice of spectral norm on a finite-dimensional algebra over a normed field. -/
noncomputable def spectralNorm : SpectralNorm 𝕜 A :=
  haveI : NeZero (Module.finrank 𝕜 A) := ⟨Module.finrank_pos.ne'⟩
  (spectralRadiusLimNorm 𝕜 _).comap
    ((algEquivMatrix (Module.finBasis 𝕜 A)).toAlgHom.comp (Algebra.lmul 𝕜 A))

/-- Type synonym to -/
private def SpectralNorm.space (_f : SpectralNorm 𝕜 A) := A
deriving Field, Algebra 𝕜

private instance (f : SpectralNorm 𝕜 A) : FiniteDimensional 𝕜 f.space :=
  inferInstanceAs (FiniteDimensional 𝕜 A)

/-- The ring norm defined by a spectral norm. -/
private def SpectralNorm.ringNorm (f : SpectralNorm 𝕜 A) : RingNorm f.space where
  toFun := f
  map_zero' := map_zero f
  add_le' := map_add_le_add f
  neg' := map_neg_eq_map f
  mul_le' := map_mul_le_mul f
  eq_zero_of_map_eq_zero' _ := eq_zero_of_map_eq_zero f

private instance (f : SpectralNorm 𝕜 A) : NormedRing f.space :=
  f.ringNorm.toNormedRing

private instance (f : SpectralNorm 𝕜 A) : NormedAlgebra 𝕜 f.space where
  norm_smul_le c x := (map_smul_eq_mul f c x).le

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [Field A] [Algebra 𝕜 A] [FiniteDimensional 𝕜 A]

private theorem spectralNorm_le [CompleteSpace 𝕜] (f g : SpectralNorm 𝕜 A) (x : A) : f x ≤ g x := by
  let T₀ : g.space ≃ₗ[𝕜] f.space := LinearEquiv.refl 𝕜 A
  let T : g.space ≃L[𝕜] f.space := T₀.toContinuousLinearEquiv
  let C := ‖T.toContinuousLinearMap‖
  have h x : f x ≤ C * g x := T.toContinuousLinearMap.le_opNorm x
  replace h : ∀ᶠ (k : ℕ) in Filter.atTop, f x ≤ C ^ (k : ℝ)⁻¹ * g x := by
    refine Filter.eventually_atTop.mpr ⟨1, fun k hk ↦ ?_⟩
    specialize h (x ^ k)
    rw [f.map_pow, g.map_pow, ← Real.rpow_natCast,
      ← Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by simp; grind),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
      mul_inv_cancel₀ (by simp; grind), Real.rpow_one] at h
    exact h
  have : Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹ * g x) atTop (𝓝 (1 * g x)) :=
    (((Real.continuous_const_rpow T.norm_pos.ne').tendsto' 0 1 C.rpow_zero).comp
      tendsto_inv_atTop_nhds_zero_nat).mul_const (g x)
  exact ge_of_tendsto (by simpa) h

/-- Uniqueness of spectral norms on a finite-dimensional algebra over a complete normed field. -/
theorem spectralNorm_unique [CompleteSpace 𝕜] (f g : SpectralNorm 𝕜 A) : f = g := by
  ext x
  exact le_antisymm (spectralNorm_le f g x) (spectralNorm_le g f x)

end NontriviallyNormedField

namespace SpectralNorm

section modification

variable [NormedField 𝕜] [Field A] [Algebra 𝕜 A]

private noncomputable def modifyAux (f : SpectralNorm 𝕜 A) (a x : A) : ℝ :=
  atTop.limUnder (fun k : ℕ ↦ f (x * a ^ k) / f a ^ k)

private theorem tendsTo_modifyAux (f : SpectralNorm 𝕜 A) (a x : A) :
    atTop.Tendsto (fun k : ℕ ↦ f (x * a ^ k) / f a ^ k) (𝓝 (f.modifyAux a x)) := by
  refine tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n ↦ ?_) ⟨0, ?_⟩⟩
  · by_cases hy : a = 0
    · rw [hy, zero_pow n.add_one_ne_zero, mul_zero, map_zero, zero_div]
      positivity
    · grw [pow_succ, ← mul_assoc, map_mul_le_mul, pow_succ, mul_div_mul_right _ _ (by simpa)]
  · rintro - ⟨x, rfl⟩
    positivity

@[simp]
private theorem modifyAux_zero (f : SpectralNorm 𝕜 A) (a : A) :
    f.modifyAux a 0 = 0 := by
  symm
  simpa using f.tendsTo_modifyAux a 0

@[simp]
private theorem modifyAux_one (f : SpectralNorm 𝕜 A) {a : A} (ha : a ≠ 0) :
    f.modifyAux a 1 = 1 := by
  symm
  simpa [ha] using f.tendsTo_modifyAux a 1

private theorem modifyAux_nonneg (f : SpectralNorm 𝕜 A) (a x : A) :
    0 ≤ f.modifyAux a x :=
  ge_of_tendsto' (f.tendsTo_modifyAux a x) fun k ↦ by positivity

private theorem modifyAux_add_le (f : SpectralNorm 𝕜 A) (a x y : A) :
    f.modifyAux a (x + y) ≤ f.modifyAux a x + f.modifyAux a y := by
  refine le_of_tendsto_of_tendsto' (f.tendsTo_modifyAux a (x + y))
    ((f.tendsTo_modifyAux a x).add (f.tendsTo_modifyAux a y)) fun k ↦ ?_
  grw [add_mul, map_add_le_add, add_div]

private theorem modifyAux_mul_le (f : SpectralNorm 𝕜 A) (a x y : A) :
    f.modifyAux a (x * y) ≤ f.modifyAux a x * f.modifyAux a y := by
  refine le_of_tendsto_of_tendsto'
    ((f.tendsTo_modifyAux a (x * y)).comp (tendsto_id.atTop_add_atTop tendsto_id))
    ((f.tendsTo_modifyAux a x).mul (f.tendsTo_modifyAux a y)) fun k ↦ ?_
  rw [Function.comp_apply, id_def, pow_add, pow_add, div_mul_div_comm, mul_mul_mul_comm]
  grw [map_mul_le_mul]

private theorem modifyAux_pow (f : SpectralNorm 𝕜 A) {a : A} (ha : a ≠ 0) (x : A) (k : ℕ) :
    f.modifyAux a (x ^ k) = f.modifyAux a x ^ k := by
  by_cases! hk : k = 0
  · simp [ha, hk]
  refine tendsto_nhds_unique_of_forall ((f.tendsTo_modifyAux a (x ^ k)).comp
    (tendsto_id.atTop_mul_const' hk.pos)) ((f.tendsTo_modifyAux a x).pow k) fun j ↦ ?_
  rw [Function.comp_apply, id_def, pow_mul, ← mul_pow, f.map_pow, pow_mul, div_pow]

private theorem modifyAux_map_smul_eq_mul (f : SpectralNorm 𝕜 A) (a : A) (c : 𝕜) (x : A) :
    f.modifyAux a (c • x) = ‖c‖ * f.modifyAux a x := by
  refine tendsto_nhds_unique_of_forall (f.tendsTo_modifyAux a (c • x))
    ((f.tendsTo_modifyAux a x).const_mul ‖c‖) fun k ↦ ?_
  rw [smul_mul_assoc, map_smul_eq_mul, mul_div]

private theorem modifyAux_mul (f : SpectralNorm 𝕜 A) (y : A) (x : A) :
    f.modifyAux y (x * y) = f.modifyAux y x * f y := by
  by_cases hy : y = 0
  · simp [hy]
  · refine tendsto_nhds_unique_of_forall (f.tendsTo_modifyAux y (x * y))
      (((f.tendsTo_modifyAux y x).mul_const (f y)).comp (tendsto_add_atTop_nat 1)) fun k ↦ ?_
    by_cases hy : y = 0
    · simp [hy]
    rw [Function.comp_apply, pow_succ', mul_assoc, pow_succ, div_mul,
      mul_div_cancel_right₀ _ (by simpa)]

open Classical in
/-- Modify a spectral norm on a field by a element of the field. -/
@[no_expose]
noncomputable def modify (f : SpectralNorm 𝕜 A) (a : A) : SpectralNorm 𝕜 A :=
  if ha : a = 0 then f else
  { toFun := f.modifyAux a
    map_zero' := f.modifyAux_zero a
    map_one' := f.modifyAux_one ha
    nonneg' := f.modifyAux_nonneg a
    map_add_le_add' x y _ := f.modifyAux_add_le a x y
    map_mul_le_mul' x y _ := f.modifyAux_mul_le a x y
    map_pow' := f.modifyAux_pow ha
    map_smul_eq_mul' := f.modifyAux_map_smul_eq_mul a }

theorem modify_mul (f : SpectralNorm 𝕜 A) (y : A) (x : A) :
    f.modify y (x * y) = f.modify y x * f y := by
  by_cases hy : y = 0
  · simp [hy]
  · dsimp only [modify]
    rw [dite_eq_right hy]
    exact f.modifyAux_mul y x

end modification

variable [NormedField 𝕜] [CompleteSpace 𝕜] [Field A] [Algebra 𝕜 A]
  [FiniteDimensional 𝕜 A]

open Classical in
/-- A spectral norm on a finite extension of a complete normed field defines an absolute value. -/
noncomputable def toAbsoluteValue (f : SpectralNorm 𝕜 A) : AbsoluteValue A ℝ :=
  if h : ∃ x : 𝕜, 1 < ‖x‖ then
  letI : NontriviallyNormedField 𝕜 := ⟨h⟩
  { __ := f
    eq_zero' _ := f.eq_zero_iff
    add_le' := map_add_le_add f
    map_mul' x y := by simpa [spectralNorm_unique (f.modify y) f] using f.modify_mul y x }
  else AbsoluteValue.trivial

theorem toAbsoluteValue_algebraMap (f : SpectralNorm 𝕜 A) (x : 𝕜) :
    f.toAbsoluteValue (algebraMap 𝕜 A x) = ‖x‖ := by
  sorry

variable (𝕜 A) in
/-- The absolute value on a finite extension of a complete normed field. -/
noncomputable def absoluteValue : AbsoluteValue A ℝ :=
  (spectralNorm 𝕜 A).toAbsoluteValue

variable (A) in
theorem absoluteValue_algebraMap (x : 𝕜) : absoluteValue 𝕜 A (algebraMap 𝕜 A x) = ‖x‖ :=
  (spectralNorm 𝕜 A).toAbsoluteValue_algebraMap x

end SpectralNorm

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [CompleteSpace (WithAbs v)]

/-- The unique extension of a complete absolue value to a finite extension. -/
noncomputable def extension : AbsoluteValue L ℝ :=
  SpectralNorm.absoluteValue (WithAbs v) L

instance : (v.extension L).LiesOver v where
  comp_eq := by
    ext x
    exact SpectralNorm.absoluteValue_algebraMap L (WithAbs.toAbs v x)

end AbsoluteValue
