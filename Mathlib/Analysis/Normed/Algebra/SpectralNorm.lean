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

In this file we prove that a spectral norm on a finite extension of a complete normed field is
multiplicative, thereby defining an absolute value. This is the key ingredient needed to extend
absolute values to finite extensions in general.

We follow the proof in a [MathOverflow answer](https://mathoverflow.net/a/419366/95685) by
Denis Nardin. The idea is to first prove uniqueness of spectral norms on finite-dimensional
algebras over complete normed fields, and then apply this uniqueness to the spectral norm
`‖x‖` and the modified spectral norm `‖x‖_y = lim_{n → ∞} ‖x * y ^ n‖ / ‖y‖ ^ n`.

## Main definitions

* `SpectralNorm 𝕜 A`: the type of all spectral norms on `A` over `𝕜`.
* `spectralNorm 𝕜 A`: construction of a spectral norm on a finite-dimensional algebra `A` over a
  normed field `𝕜`.
* `SpectralNorm.toAbsoluteValue f`: a spectral norm on a finite extension of a complete normed field
  defines an absolute value.

## Main statements

* `spectralNorm_unique`: uniqueness of spectral norms on a finite-dimensional algebra.

-/

@[expose] public section

-- todo: check if this has utility elsewhere in the library
open Filter Topology in
theorem tendsto_nhds_unique_of_forall {X Y : Type*} [TopologicalSpace X] [T2Space X] {f g : Y → X}
    {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b))
    (hfg : ∀ y, f y = g y) : a = b :=
  tendsto_nhds_unique_of_eventuallyEq ha hb (Eventually.of_forall hfg)

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
  mul_le' x y : toFun (x * y) ≤ toFun x * toFun y
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
/-- Construction of a spectral norm on a finite-dimensional algebra `A` over a normed field `𝕜`. -/
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

section Field

variable [Field A] [Algebra 𝕜 A]

namespace SpectralNorm

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

private theorem tendsTo_modifyAux' (f : SpectralNorm 𝕜 A) (a x : A) :
    atTop.Tendsto (fun k : ℕ+ ↦ f (x * a ^ (k : ℕ)) / f a ^ (k : ℕ)) (𝓝 (f.modifyAux a x)) :=
  PNat.tendsto_comp_val_iff.mpr (f.tendsTo_modifyAux a x)

private theorem modifyAux_zero_apply (f : SpectralNorm 𝕜 A) (x : A) : f.modifyAux 0 x = 0 := by
  symm
  simpa using f.tendsTo_modifyAux' 0 x

@[simp]
private theorem modifyAux_zero (f : SpectralNorm 𝕜 A) : f.modifyAux 0 = 0 := by
  ext x
  exact f.modifyAux_zero_apply x

private theorem modifyAux_one_apply (f : SpectralNorm 𝕜 A) (x : A) : f.modifyAux 1 x = f x := by
  symm
  simpa using f.tendsTo_modifyAux 1 x

@[simp]
private theorem modifyAux_one (f : SpectralNorm 𝕜 A) : f.modifyAux 1 = f := by
  ext x
  exact f.modifyAux_one_apply x

@[simp]
private theorem modifyAux_apply_zero (f : SpectralNorm 𝕜 A) (a : A) :
    f.modifyAux a 0 = 0 := by
  symm
  simpa using f.tendsTo_modifyAux a 0

@[simp]
private theorem modifyAux_apply_one (f : SpectralNorm 𝕜 A) {a : A} (ha : a ≠ 0) :
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

private theorem modifyAux_eq_zero {f : SpectralNorm 𝕜 A} {a x : A} (ha : a ≠ 0) :
    f.modifyAux a x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have h := f.modifyAux_mul_le a x x⁻¹
    contrapose! h
    simp [ha, hx, h]
  · simp [hx]

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
    map_one' := f.modifyAux_apply_one ha
    nonneg' := f.modifyAux_nonneg a
    eq_zero' x := modifyAux_eq_zero ha
    add_le' := f.modifyAux_add_le a
    mul_le' := f.modifyAux_mul_le a
    map_pow' := f.modifyAux_pow ha
    map_smul_eq_mul' := f.modifyAux_map_smul_eq_mul a }

theorem modify_mul (f : SpectralNorm 𝕜 A) (y : A) (x : A) :
    f.modify y (x * y) = f.modify y x * f y := by
  by_cases hy : y = 0
  · simp [hy]
  · dsimp only [modify]
    rw [dite_eq_right hy]
    exact f.modifyAux_mul y x

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 A]

/-- A spectral norm on a finite extension of a complete normed field defines an absolute value. -/
def toAbsoluteValue (f : SpectralNorm 𝕜 A) : AbsoluteValue A ℝ where
  __ := f
  map_mul' x y := by simpa [spectralNorm_unique (f.modify y) f] using f.modify_mul y x

end SpectralNorm

end Field
