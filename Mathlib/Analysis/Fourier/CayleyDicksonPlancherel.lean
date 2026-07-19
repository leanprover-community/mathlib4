/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Algebra.Octonion
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for hypercomplex Fourier transforms on the Cayley–Dickson tower

The (left-sided) hypercomplex Fourier transform of a function `f : V → CayleyDickson A`
on a finite-dimensional real inner product space `V` replaces the imaginary unit in the
Fourier kernel by the Cayley–Dickson doubling unit `ℓ`:

`ℱ f ξ = ∫ x, exp (-2π ⟪x, ξ⟫ ℓ) * f x
       = ∫ x, (cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ℓ) * f x`.

Cayley–Dickson algebras beyond the quaternions are not associative — the sedenions are
not even alternative and have zero divisors — but the Fourier theory only needs a complex
*module* structure on the codomain. Left multiplication by `ℓ` squares to `-1` at every
level of the tower (`CayleyDickson.unit_mul_unit_mul`), so `Complex.liftAux` into
`Module.End ℝ (CayleyDickson A)` — where associativity lives — makes every Cayley–Dickson
algebra a complex vector space. Equipping it with a compatible complex Hilbert space
structure, Plancherel's theorem and the Fourier inversion formula are inherited from the
vector-valued case.

Taking `A = ℍ[ℝ]` gives the octonion Fourier transform (Hahn–Snopek, Błaszczyk),
`A = Octonion ℝ` the sedenion one, and so on up the tower.

## Main definitions

* `CayleyDickson.fourierIntegral`: the hypercomplex Fourier transform, defined by the
  real cos/sin kernel above.
* `CayleyDickson.fourierInvIntegral`: its inverse.
* `CayleyDickson.fourierL2`: the hypercomplex Fourier transform as a linear isometry
  equivalence of `L²(V, CayleyDickson A)`.

## Main statements

* `CayleyDickson.fourierIntegral_eq_fourier`: the hypercomplex Fourier transform is the
  Fourier transform for the `ℓ`-complex structure.
* `CayleyDickson.integral_norm_sq_fourierIntegral`: Plancherel's theorem for Schwartz
  functions.
* `CayleyDickson.fourierInvIntegral_fourierIntegral`: the Fourier inversion formula for
  Schwartz functions.

## References

* S. L. Hahn, K. M. Snopek, *The unified theory of n-dimensional complex and
  hypercomplex analytic signals*, Bull. Polish Ac. Sci. 59 (2011)
* Ł. Błaszczyk, *Octonion Fourier transform of real-valued functions of three
  variables*, J. Fourier Anal. Appl. 26 (2020)

-/

@[expose] public section

noncomputable section

open Quaternion MeasureTheory SchwartzMap Real
open scoped FourierTransform RealInnerProductSpace

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A] [Module ℝ A] [StarModule ℝ A]
  [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

/-! ### The complex structure -/

/-- Left multiplication by the doubling unit `ℓ`, as a real-linear endomorphism. -/
def unitMulHom : Module.End ℝ (CayleyDickson A) where
  toFun x := unit A * x
  map_add' := mul_add _
  map_smul' r x := mul_smul_comm' r _ x

@[simp] theorem unitMulHom_apply (x : CayleyDickson A) : unitMulHom x = unit A * x := rfl

theorem unitMulHom_mul_unitMulHom :
    unitMulHom * unitMulHom = (-1 : Module.End ℝ (CayleyDickson A)) := by
  ext x : 1
  simp [Module.End.mul_apply]

/-- The real-algebra morphism `ℂ →ₐ[ℝ] Module.End ℝ (CayleyDickson A)` sending `I` to
left multiplication by the doubling unit. The endomorphism algebra is associative even
when the Cayley–Dickson algebra is not, which is all `Complex.liftAux` needs. -/
def complexLift : ℂ →ₐ[ℝ] Module.End ℝ (CayleyDickson A) :=
  Complex.liftAux unitMulHom unitMulHom_mul_unitMulHom

/-- Every Cayley–Dickson algebra is a complex vector space, `I` acting by left
multiplication by the doubling unit `ℓ`. It is in general *not* a complex algebra: `ℓ`
is not central, but a module structure needs no commutation.

This is a scoped instance since it involves the choice of an imaginary unit. -/
scoped instance instModuleComplex : Module ℂ (CayleyDickson A) :=
  Module.compHom _ (complexLift (A := A)).toRingHom

theorem complex_smul_def (z : ℂ) (x : CayleyDickson A) : z • x = complexLift z x := rfl

/-- The complex scalar action, componentwise. -/
theorem complex_smul_mk (z : ℂ) (x : CayleyDickson A) :
    z • x = ⟨z.re • x.fst - z.im • star x.snd, z.re • x.snd + z.im • star x.fst⟩ := by
  rw [complex_smul_def, complexLift, Complex.liftAux_apply]
  ext <;>
    simp [Module.algebraMap_end_apply, unit_mul, sub_eq_add_neg]

scoped instance : IsScalarTower ℝ ℂ (CayleyDickson A) :=
  ⟨fun r z x => by
    rw [complex_smul_def, complex_smul_def, map_smul, LinearMap.smul_apply]⟩

scoped instance : SMulCommClass ℂ ℂ (CayleyDickson A) :=
  ⟨fun z w x => by
    rw [complex_smul_def, complex_smul_def, complex_smul_def, complex_smul_def,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm z w]⟩

instance [Module.Finite ℝ A] : Module.Finite ℂ (CayleyDickson A) := by
  -- pin the native real module structure (rather than the one restricted from `ℂ`)
  letI : Module ℝ (CayleyDickson A) := CayleyDickson.instModule
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-! ### The Hilbert space structure -/

variable [Module.Finite ℝ A]

/-- A `ℂ`-linear equivalence with a complex Euclidean space, fixing a Hilbert space
structure. (Plancherel's theorem below holds for any choice.) -/
def toEuclidean :
    CayleyDickson A ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ (CayleyDickson A))) :=
  (Module.finBasis ℂ _).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

scoped instance instNormedAddCommGroup : NormedAddCommGroup (CayleyDickson A) :=
  NormedAddCommGroup.induced _ _ (toEuclidean (A := A)).toLinearMap
    (toEuclidean (A := A)).injective

scoped instance instInnerProductSpace : InnerProductSpace ℂ (CayleyDickson A) :=
  InnerProductSpace.induced (toEuclidean (A := A)).toLinearMap

scoped instance instCompleteSpace : CompleteSpace (CayleyDickson A) :=
  FiniteDimensional.complete ℂ _

/-! ### The hypercomplex Fourier transform -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [Module.Finite ℝ A] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The hypercomplex Fourier kernel
`exp (-2π ⟪x, ξ⟫ ℓ) = cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ℓ`, componentwise. -/
def fourierKernel (x ξ : V) : CayleyDickson A :=
  ⟨Real.cos (2 * π * ⟪x, ξ⟫) • 1, -(Real.sin (2 * π * ⟪x, ξ⟫) • 1)⟩

omit [Module.Finite ℝ A] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The inverse hypercomplex Fourier kernel `exp (2π ⟪x, ξ⟫ ℓ)`. -/
def fourierInvKernel (x ξ : V) : CayleyDickson A :=
  ⟨Real.cos (2 * π * ⟪x, ξ⟫) • 1, Real.sin (2 * π * ⟪x, ξ⟫) • 1⟩

/-- The (left-sided) hypercomplex Fourier transform. -/
def fourierIntegral (f : V → CayleyDickson A) (ξ : V) : CayleyDickson A :=
  ∫ x, fourierKernel x ξ * f x

/-- The inverse hypercomplex Fourier transform. -/
def fourierInvIntegral (f : V → CayleyDickson A) (ξ : V) : CayleyDickson A :=
  ∫ x, fourierInvKernel x ξ * f x

omit [Module.Finite ℝ A] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar action of the Fourier character is left multiplication by the
hypercomplex Fourier kernel. -/
theorem exp_smul_eq_fourierKernel_mul (x ξ : V) (a : CayleyDickson A) :
    Complex.exp (((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I) • a
      = fourierKernel x ξ * a := by
  rw [complex_smul_mk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ext <;>
    simp [fourierKernel, smul_mul_assoc, mul_smul_comm, sub_eq_add_neg]

omit [Module.Finite ℝ A] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar action of the inverse Fourier character is left multiplication by the
inverse hypercomplex Fourier kernel. -/
theorem exp_smul_eq_fourierInvKernel_mul (x ξ : V) (a : CayleyDickson A) :
    Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • a
      = fourierInvKernel x ξ * a := by
  rw [complex_smul_mk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ext <;>
    simp [fourierInvKernel, smul_mul_assoc, mul_smul_comm, sub_eq_add_neg]

/-- The hypercomplex Fourier transform is the Fourier transform of a vector-valued
function, for the complex structure given by the doubling unit. -/
theorem fourierIntegral_eq_fourier (f : V → CayleyDickson A) (ξ : V) :
    fourierIntegral f ξ = 𝓕 f ξ := by
  rw [Real.fourier_eq', fourierIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change fourierKernel x ξ * f x
    = Complex.exp (((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • f x
  rw [show ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I
        = ((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I by norm_num,
    exp_smul_eq_fourierKernel_mul]

/-- The inverse hypercomplex Fourier transform is the inverse Fourier transform of a
vector-valued function, for the complex structure given by the doubling unit. -/
theorem fourierInvIntegral_eq_fourierInv (f : V → CayleyDickson A) (ξ : V) :
    fourierInvIntegral f ξ = 𝓕⁻ f ξ := by
  rw [Real.fourierInv_eq', fourierInvIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change fourierInvKernel x ξ * f x
    = Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • f x
  rw [exp_smul_eq_fourierInvKernel_mul]

/-! ### Plancherel's theorem and inversion -/

theorem fourierIntegral_coe (f : 𝓢(V, CayleyDickson A)) (ξ : V) :
    fourierIntegral (⇑f) ξ = 𝓕 f ξ := by
  rw [fourierIntegral_eq_fourier, fourier_coe]

/-- **Plancherel's theorem** for the hypercomplex Fourier transform of Schwartz
functions, inner product version. -/
theorem integral_inner_fourierIntegral_fourierIntegral (f g : 𝓢(V, CayleyDickson A)) :
    ∫ ξ, inner ℂ (fourierIntegral (⇑f) ξ) (fourierIntegral (⇑g) ξ)
      = ∫ x, inner ℂ (f x) (g x) := by
  simp_rw [fourierIntegral_coe]
  exact integral_inner_fourier_fourier f g

/-- **Plancherel's theorem** for the hypercomplex Fourier transform of Schwartz
functions: the transform preserves the `L²` norm. -/
theorem integral_norm_sq_fourierIntegral (f : 𝓢(V, CayleyDickson A)) :
    ∫ ξ, ‖fourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [fourierIntegral_coe]
  exact integral_norm_sq_fourier f

/-- **Fourier inversion** for the hypercomplex Fourier transform of Schwartz
functions. -/
theorem fourierInvIntegral_fourierIntegral (f : 𝓢(V, CayleyDickson A)) (x : V) :
    fourierInvIntegral (fourierIntegral (⇑f)) x = f x := by
  have h : fourierIntegral (⇑f) = 𝓕 (⇑f) :=
    funext fun ξ => fourierIntegral_eq_fourier _ ξ
  rw [h, fourierInvIntegral_eq_fourierInv, ← fourier_coe, ← fourierInv_coe,
    FourierPair.fourierInv_fourier_eq f]

/-- **Fourier inversion** for the hypercomplex Fourier transform of Schwartz
functions, the other composition. -/
theorem fourierIntegral_fourierInvIntegral (f : 𝓢(V, CayleyDickson A)) (x : V) :
    fourierIntegral (fourierInvIntegral (⇑f)) x = f x := by
  have h : fourierInvIntegral (⇑f) = 𝓕⁻ (⇑f) :=
    funext fun ξ => fourierInvIntegral_eq_fourierInv _ ξ
  rw [h, fourierIntegral_eq_fourier, ← fourierInv_coe, ← fourier_coe,
    FourierInvPair.fourier_fourierInv_eq f]

/-! ### `L²` theory -/

variable (A V) in
/-- The hypercomplex Fourier transform as a linear isometry equivalence of
`L²(V, CayleyDickson A)` — the `L²` form of **Plancherel's theorem**. -/
def fourierL2 :
    Lp (α := V) (CayleyDickson A) 2 ≃ₗᵢ[ℂ] Lp (α := V) (CayleyDickson A) 2 :=
  Lp.fourierTransformₗᵢ _ _

@[simp] theorem norm_fourierL2_eq (f : Lp (α := V) (CayleyDickson A) 2) :
    ‖fourierL2 A V f‖ = ‖f‖ :=
  (fourierL2 A V).norm_map f

end CayleyDickson

/-! ### The octonion and sedenion Fourier transforms

The hypothesis chain of the generic results is satisfied at every level of the
Cayley–Dickson tower over the quaternions, so Plancherel's theorem specializes to the
octonion Fourier transform, the sedenion one, and so on. We record the sedenion case —
an algebra with zero divisors that is not even alternative — explicitly. -/

section Instances

open CayleyDickson in
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (f : 𝓢(V, Octonion ℝ)) :
    ∫ ξ, ‖fourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  integral_norm_sq_fourierIntegral f

open CayleyDickson in
/-- **Plancherel's theorem for the sedenion Fourier transform.** The sedenions have zero
divisors and are not alternative, but the doubling unit is still a square root of `-1`
by direct computation, which is all the Fourier theory needs. -/
theorem Sedenion.integral_norm_sq_fourierIntegral (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, Sedenion ℝ)) :
    ∫ ξ, ‖fourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  CayleyDickson.integral_norm_sq_fourierIntegral f

open CayleyDickson in
/-- **Fourier inversion for the sedenion Fourier transform.** -/
theorem Sedenion.fourierInvIntegral_fourierIntegral (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, Sedenion ℝ)) (x : V) :
    fourierInvIntegral (fourierIntegral (⇑f)) x = f x :=
  CayleyDickson.fourierInvIntegral_fourierIntegral f x

end Instances
