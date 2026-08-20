/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.SpectralRadiusLimit
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

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

-- todo: check if this has utility elsewhere in the library
open Filter Topology in
theorem tendsto_nhds_unique_of_forall {X Y : Type*} [TopologicalSpace X] [T2Space X] {f g : Y → X}
    {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b))
    (hfg : ∀ y, f y = g y) : a = b :=
  tendsto_nhds_unique_of_eventuallyEq ha hb (Eventually.of_forall hfg)

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

variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Field A] [Algebra 𝕜 A]
  [FiniteDimensional 𝕜 A]

/-- A spectral norm on a finite extension of a complete normed field defines an absolute value. -/
def toAbsoluteValue (f : SpectralNorm 𝕜 A) : AbsoluteValue A ℝ where
  __ := f
  eq_zero' _ := f.eq_zero_iff
  add_le' := map_add_le_add f
  map_mul' x y := by simpa [spectralNorm_unique (f.modify y) f] using f.modify_mul y x

/-- The absolute value on a finite extension of a complete normed field. -/
noncomputable def absoluteValue : AbsoluteValue A ℝ :=
  (spectralNorm 𝕜 A).toAbsoluteValue

end SpectralNorm
