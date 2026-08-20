/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Algebra.SpectralRadiusLimit
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Subadditive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.UniformField

/-!
# Spectral norms and extensions of absolute values

This file defines spectral norms and uses them to construct extensions of absolute values.

If `A` is an algebra over a normed field `𝕜`, then a spectral norm on `A` over `𝕜` is
a `𝕜`-vector space norm on `A` satisfying `‖x * y‖ ≤ ‖x‖ * ‖y‖` and `‖x ^ k‖ = ‖x‖ ^ k`.

In this file we prove that a spectral norm on a finite-dimensional algebra `A` over a complete
normed field `𝕜` is multiplicative, thereby defining an absolute value on `A`. This is the key
ingredient needed for extending absolute values to finite field extensions.

This proof is taken from a [MathOverflow answer](https://mathoverflow.net/a/419366/95685) by
Denis Nardin. The idea is to first prove uniqueness of spectral norms on finite-dimensional
algebras over complete normed fields, and then apply this uniqueness to the spectral norm
`‖x‖` and the modified spectral norm `‖x‖_y = lim_{n → ∞} ‖x * y ^ n‖ * ‖y‖ ^ (-n)`.

## Main definitions

* `SpectralNorm 𝕜 A`: the type of all spectral norms on `A` over `𝕜`.

## Main statements

* `spectralNorm_unique`: any two spectral norms on a finite-dimensional algebra over a complete
* `tendsto_spectralRadiusLim`: the sequence `‖a ^ k‖ ^ (1 / k)` converges to `spectralRadiusLimit`.
* `spectralRadiusLim_add_le`: `spectralRadiusLimit` is subadditive.
* `spectralRadiusLim_mul_le`: `spectralRadiusLimit` is submultiplicative.

-/

@[expose] public section

@[simp]
theorem Filter.limUnder_const {X α : Type*} [TopologicalSpace X] [Nonempty X] [T2Space X]
    (f : Filter α) [f.NeBot] (x : X) : (f.limUnder fun _ ↦ x) = x :=
  tendsto_const_nhds.limUnder_eq

open Filter

open scoped Topology

variable {𝕜 A : Type*} [NormedField 𝕜]

section Ring

variable [Ring A] [Algebra 𝕜 A]

variable (𝕜 A) in
/-- The type of all spectral norms on `A` over `𝕜`. -/
@[ext]
structure SpectralNorm extends OneHom A ℝ where
  nonneg' x : 0 ≤ toFun x
  eq_zero' x : toFun x = 0 ↔ x = 0
  add_le' x y : toFun (x + y) ≤ toFun x + toFun y
  mul_le' x y : toFun (x * y) ≤ toFun x * toFun y -- maybe only for commuting pairs x and y?
  map_pow' x k : toFun (x ^ k) = toFun x ^ k
  map_smul_eq_mul' (c : 𝕜) x : toFun (c • x) = ‖c‖ * toFun x

namespace SpectralNorm

instance : FunLike (SpectralNorm 𝕜 A) A ℝ where
  coe f := f.toFun
  coe_injective _ _ := SpectralNorm.ext

@[simp]
theorem coe_toOneHom (f : SpectralNorm 𝕜 A) : ⇑f.toOneHom = f := rfl

instance : OneHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_one f := f.map_one'

@[simp]
protected theorem eq_zero {f : SpectralNorm 𝕜 A} {x : A} : f x = 0 ↔ x = 0 :=
  f.eq_zero' x

instance : SubmultiplicativeHomClass (SpectralNorm 𝕜 A) A ℝ where
  map_mul_le_mul := mul_le'

@[simp]
protected theorem map_pow (f : SpectralNorm 𝕜 A) (x : A) (k : ℕ) : f (x ^ k) = f x ^ k :=
  f.map_pow' x k

instance : SeminormClass (SpectralNorm 𝕜 A) 𝕜 A where
  map_add_le_add := add_le'
  map_zero f := f.eq_zero.mpr rfl
  map_neg_eq_map f x := by simpa using f.map_smul_eq_mul' (-1) x
  map_smul_eq_mul := map_smul_eq_mul'

end SpectralNorm

variable [FiniteDimensional 𝕜 A]

variable (𝕜 A) in
/-- Construction of a spectral norm on a finite-dimensional algebra. -/
def spectralNorm : SpectralNorm 𝕜 A := by
  -- use `spectralRadiusLim`
  sorry

variable [CompleteSpace 𝕜]

/-- Any two spectral norms on a finite-dimensional algebra over a complete normed field coincide. -/
theorem spectralNorm_unique (f g : SpectralNorm 𝕜 A) :
    f = g := by
  -- use equivalence of norms
  sorry

end Ring

section DivisionRing

variable [DivisionRing A] [Algebra 𝕜 A]

namespace SpectralNorm

noncomputable def modifyAux (f : SpectralNorm 𝕜 A) (y x : A) : ℝ :=
  atTop.limUnder (fun k : ℕ ↦ f (x * y ^ k) * f y ^ (-k : ℤ))

theorem tendsTo_modifyAux (f : SpectralNorm 𝕜 A) (y x : A) :
    atTop.Tendsto (fun k : ℕ ↦ f (x * y ^ k) * f y ^ (-k : ℤ)) (𝓝 (f.modifyAux y x)) := by
  refine tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n ↦ ?_) ⟨0, ?_⟩⟩
  · by_cases hy : y = 0
    · rw [hy, zero_pow n.add_one_ne_zero, mul_zero, map_zero, zero_mul]
      positivity
    · grw [pow_succ, ← mul_assoc, map_mul_le_mul, mul_assoc, ← zpow_one_add₀ (mt f.eq_zero.mp hy)]
      simp
  · rintro - ⟨x, rfl⟩
    positivity

/-- Modify a spectral norm on a division ring by a nonzero element. -/
noncomputable def modify (f : SpectralNorm 𝕜 A) {y : A} (hy : y ≠ 0) :
    SpectralNorm 𝕜 A where
  toFun := f.modifyAux y
  map_one' := .symm <| by simpa [mt f.eq_zero.mp hy] using f.tendsTo_modifyAux y 1
  nonneg' x := sorry
  eq_zero' x := sorry
  add_le' x y := sorry
  mul_le' x y := sorry
  map_pow' x k := sorry
  map_smul_eq_mul' c x := sorry

theorem modify_mul (f : SpectralNorm 𝕜 A) {y : A} (hy : y ≠ 0) (x : A) :
    f.modify hy (x * y) = f.modify hy x * f y := by
  sorry

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 A]

/-- A spectral norm on a finite-dimensional division ring over a complete normed field defines an
absolute value. -/
def toAbsoluteValue (f : SpectralNorm 𝕜 A) : AbsoluteValue A ℝ where
  __ := f
  map_mul' x y := by
    by_cases hy : y = 0
    · simp [hy]
    · simpa [spectralNorm_unique (f.modify hy) f] using f.modify_mul hy x

end SpectralNorm

end DivisionRing
