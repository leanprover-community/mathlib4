/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral norms and extensions of absolute values

This file defines spectral norms and uses them to construct extensions of absolute values.

For a normed algebra `A` with `‖1‖ = 1` over a normed field `𝕜`, the spectral radius limit
`lim ‖x ^ k‖ ^ (1 / k)` defines a function `f : A → ℝ` satisfying the following properties:
* `f 0 = 0`,
* `f 1 = 1`,
* `0 ≤ f x` for all `x : A`,
* `f (x + y) ≤ f x + f y` for all commuting `x y : A`,
* `f (x * y) ≤ f x * f y` for all commuting `x y : A`,
* `f (x ^ k) = (f x) ^ k` for all `x : A` and `k : ℕ`,
* `f (c • x) = ‖c‖ * f x` for all `c : 𝕜` and `x : A`.

In general, if `A` is an algebra over a normed field `𝕜`, then a function `f : A → ℝ` satisfying
these properties is called a **spectral norm**.

For a finite-dimensional algebra over a complete normed field, the spectral norm is unique
(see `spectralNorm_unique`).

This file follows a [MathOverflow answer](https://mathoverflow.net/a/419366/95685) by Denis Nardin.

## Main definitions

* `SpectralNorm 𝕜 A`: the type of all spectral norms on `A` over `𝕜`.

## Main statements

* `spectralNorm_unique`: uniqueness of spectral norms on a finite-dimensional algebra over a
  complete normed field.
-/

@[expose] public section

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

attribute [nolint docBlame] SpectralNorm.toZeroHom

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
  · have : Commute x x⁻¹ := Commute.inv_right₀ rfl
    have h := f.map_mul_le_mul this
    contrapose! h
    simp [h, hx]
  · rw [hx, map_zero]

instance [SeminormedCommRing 𝕜] [NormOneClass 𝕜] [Field A] [Algebra 𝕜 A] :
    RingNormClass (SpectralNorm 𝕜 A) A ℝ where
  eq_zero_of_map_eq_zero f := f.eq_zero_iff.mp

section NormedField

variable [NormedField 𝕜] [Field A] [Algebra 𝕜 A] [FiniteDimensional 𝕜 A]

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
