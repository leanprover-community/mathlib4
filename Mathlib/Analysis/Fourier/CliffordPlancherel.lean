/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Analysis.CliffordAlgebra.Euclidean
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for the Clifford–Fourier transform

The Clifford–Fourier transform (Ebling–Scheuermann) of a function
`f : ℝⁿ → Cl(n,0)` replaces the imaginary unit in the Fourier kernel by the
pseudoscalar `ω = e₀ ⋯ eₙ₋₁` of the Clifford algebra:

`ℱ f ξ = ∫ x, exp (-2π ⟪x, ξ⟫ ω) * f x
       = ∫ x, (cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ω) * f x`.

For `n ≡ 2, 3 [MOD 4]` the pseudoscalar satisfies `ω² = -1`, so *left
multiplication* by the kernel is complex scalar multiplication for the complex
vector space structure on `Cl(n,0)` induced by `ω`
(`CliffordAlgebra.Euclidean.instModuleComplex`) — this needs no commutation, so
it covers both the central case `n ≡ 3 [MOD 4]` (e.g. the three-dimensional
transform of Ebling–Scheuermann) and the non-central case `n ≡ 2 [MOD 4]`
(e.g. the two-dimensional transform, where `ω` anticommutes with vectors).
Equipping the Clifford algebra with a compatible complex Hilbert space
structure, Plancherel's theorem and the Fourier inversion formula are inherited
from the vector-valued case.

## Main definitions

* `CliffordAlgebra.Euclidean.cliffordFourierIntegral`: the Clifford–Fourier
  transform, defined by the real cos/sin kernel above (no complex structure
  appears in the definition).
* `CliffordAlgebra.Euclidean.cliffordFourierInvIntegral`: the inverse
  Clifford–Fourier transform.
* `CliffordAlgebra.Euclidean.cliffordFourierL2`: the Clifford–Fourier transform
  as a linear isometry equivalence of `L²(ℝⁿ, Cl(n,0))`.

## Main statements

* `CliffordAlgebra.Euclidean.cliffordFourierIntegral_eq_fourier`: the
  Clifford–Fourier transform is the Fourier transform for the pseudoscalar
  complex structure.
* `CliffordAlgebra.Euclidean.integral_inner_cliffordFourier_cliffordFourier`:
  Plancherel's theorem for Schwartz functions.
* `CliffordAlgebra.Euclidean.integral_norm_sq_cliffordFourier`: Plancherel's
  theorem for Schwartz functions, norm version.
* `CliffordAlgebra.Euclidean.cliffordFourierInv_cliffordFourier`: the Fourier
  inversion formula for Schwartz functions.
* `CliffordAlgebra.Euclidean.norm_cliffordFourierL2_eq`: Plancherel's theorem
  on `L²`.

## References

* J. Ebling, G. Scheuermann, *Clifford Fourier transform on vector fields*,
  IEEE Transactions on Visualization and Computer Graphics 11 (2005)
* F. Brackx, N. De Schepper, F. Sommen, *The Clifford-Fourier transform*,
  J. Fourier Anal. Appl. 11 (2005)

-/

@[expose] public section

noncomputable section

open CliffordAlgebra MeasureTheory SchwartzMap Real
open scoped FourierTransform RealInnerProductSpace

namespace CliffordAlgebra.Euclidean

variable {n : ℕ} [Fact (n % 4 = 2 ∨ n % 4 = 3)]

/-! ### Finite dimensionality -/

instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

instance : Module.Finite ℂ (CliffordAlgebra (Q n)) := by
  -- pin the *native* real module structure of the Clifford algebra (rather than
  -- the one restricted from `ℂ`, which is only propositionally equal to it)
  letI : Module ℝ (CliffordAlgebra (Q n)) := Algebra.toModule
  haveI : Module.Finite ℝ (ExteriorAlgebra ℝ (EuclideanSpace ℝ (Fin n))) :=
    Module.Finite.of_basis ((PiLp.basisFun 2 ℝ (Fin n)).ExteriorAlgebra)
  haveI : Module.Finite ℝ (CliffordAlgebra (Q n)) :=
    Module.Finite.equiv (equivExterior (Q n)).symm
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-! ### The Hilbert space structure

We fix a complex Hilbert space structure on `Cl(n,0)` compatible with the
pseudoscalar complex structure by transporting the one of
`EuclideanSpace ℂ (Fin 2^(n-1))` along a `ℂ`-basis. (Plancherel's theorem below
holds for any such choice.) -/

variable (n) in
/-- A `ℂ`-linear equivalence of `Cl(n,0)` with a complex Euclidean space,
fixing a Hilbert space structure. -/
def toEuclidean :
    CliffordAlgebra (Q n) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ (CliffordAlgebra (Q n)))) :=
  (Module.finBasis ℂ _).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

scoped instance instNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra (Q n)) :=
  NormedAddCommGroup.induced _ _ (toEuclidean n).toLinearMap
    (toEuclidean n).injective

scoped instance instInnerProductSpace : InnerProductSpace ℂ (CliffordAlgebra (Q n)) :=
  InnerProductSpace.induced (toEuclidean n).toLinearMap

scoped instance instCompleteSpace : CompleteSpace (CliffordAlgebra (Q n)) :=
  FiniteDimensional.complete ℂ _

/-! ### The Clifford–Fourier transform -/

/-- The Clifford–Fourier kernel
`exp (-2π ⟪x, ξ⟫ ω) = cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ω`, where `ω` is the
pseudoscalar. Defined by ring operations only, so it does not depend on any
choice of analytic structure on the Clifford algebra. -/
def cliffordFourierKernel (x ξ : EuclideanSpace ℝ (Fin n)) : CliffordAlgebra (Q n) :=
  algebraMap ℝ _ (Real.cos (2 * π * ⟪x, ξ⟫))
    - algebraMap ℝ _ (Real.sin (2 * π * ⟪x, ξ⟫)) * pseudoscalar n

/-- The inverse Clifford–Fourier kernel `exp (2π ⟪x, ξ⟫ ω)`. -/
def cliffordFourierInvKernel (x ξ : EuclideanSpace ℝ (Fin n)) : CliffordAlgebra (Q n) :=
  algebraMap ℝ _ (Real.cos (2 * π * ⟪x, ξ⟫))
    + algebraMap ℝ _ (Real.sin (2 * π * ⟪x, ξ⟫)) * pseudoscalar n

/-- The Clifford–Fourier transform on `ℝⁿ` (Ebling–Scheuermann): the Fourier
kernel `exp (-2π ⟪x, ξ⟫ ω)` multiplies from the left. -/
def cliffordFourierIntegral (f : EuclideanSpace ℝ (Fin n) → CliffordAlgebra (Q n))
    (ξ : EuclideanSpace ℝ (Fin n)) : CliffordAlgebra (Q n) :=
  ∫ x, cliffordFourierKernel x ξ * f x

/-- The inverse Clifford–Fourier transform on `ℝⁿ`. -/
def cliffordFourierInvIntegral (f : EuclideanSpace ℝ (Fin n) → CliffordAlgebra (Q n))
    (ξ : EuclideanSpace ℝ (Fin n)) : CliffordAlgebra (Q n) :=
  ∫ x, cliffordFourierInvKernel x ξ * f x

/-- Complex scalar multiplication on `Cl(n,0)` written with ring operations. -/
theorem complex_smul_eq_mul (z : ℂ) (a : CliffordAlgebra (Q n)) :
    z • a = (algebraMap ℝ _ z.re + algebraMap ℝ _ z.im * pseudoscalar n) * a := by
  rw [complex_smul_def, complexLift_apply, Algebra.smul_def]

/-- The scalar action of the Fourier character is left multiplication by the
Clifford–Fourier kernel. -/
theorem exp_smul_eq_cliffordFourierKernel_mul (x ξ : EuclideanSpace ℝ (Fin n))
    (a : CliffordAlgebra (Q n)) :
    Complex.exp (((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I) • a
      = cliffordFourierKernel x ξ * a := by
  rw [complex_smul_eq_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg, map_neg, neg_mul, ← sub_eq_add_neg, cliffordFourierKernel]

/-- The scalar action of the inverse Fourier character is left multiplication
by the inverse Clifford–Fourier kernel. -/
theorem exp_smul_eq_cliffordFourierInvKernel_mul (x ξ : EuclideanSpace ℝ (Fin n))
    (a : CliffordAlgebra (Q n)) :
    Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • a
      = cliffordFourierInvKernel x ξ * a := by
  rw [complex_smul_eq_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    cliffordFourierInvKernel]

/-- The Clifford–Fourier transform is the Fourier transform of a vector-valued
function, for the complex structure on `Cl(n,0)` given by the pseudoscalar. -/
theorem cliffordFourierIntegral_eq_fourier
    (f : EuclideanSpace ℝ (Fin n) → CliffordAlgebra (Q n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    cliffordFourierIntegral f ξ = 𝓕 f ξ := by
  rw [Real.fourier_eq', cliffordFourierIntegral]
  congr 1 with x
  rw [show ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I
        = ((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I by norm_num,
    exp_smul_eq_cliffordFourierKernel_mul]

/-- The inverse Clifford–Fourier transform is the inverse Fourier transform of
a vector-valued function, for the complex structure on `Cl(n,0)` given by the
pseudoscalar. -/
theorem cliffordFourierInvIntegral_eq_fourierInv
    (f : EuclideanSpace ℝ (Fin n) → CliffordAlgebra (Q n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    cliffordFourierInvIntegral f ξ = 𝓕⁻ f ξ := by
  rw [Real.fourierInv_eq', cliffordFourierInvIntegral]
  congr 1 with x
  rw [exp_smul_eq_cliffordFourierInvKernel_mul]

/-! ### Plancherel's theorem -/

theorem cliffordFourierIntegral_coe (f : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n)))
    (ξ : EuclideanSpace ℝ (Fin n)) :
    cliffordFourierIntegral (⇑f) ξ = 𝓕 f ξ := by
  rw [cliffordFourierIntegral_eq_fourier, fourier_coe]

/-- **Plancherel's theorem** for the Clifford–Fourier transform of Schwartz
functions `ℝⁿ → Cl(n,0)`, inner product version. -/
theorem integral_inner_cliffordFourier_cliffordFourier
    (f g : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n))) :
    ∫ ξ, inner ℂ (cliffordFourierIntegral (⇑f) ξ) (cliffordFourierIntegral (⇑g) ξ)
      = ∫ x, inner ℂ (f x) (g x) := by
  simp_rw [cliffordFourierIntegral_coe]
  exact integral_inner_fourier_fourier f g

/-- **Plancherel's theorem** for the Clifford–Fourier transform of Schwartz
functions `ℝⁿ → Cl(n,0)`: the Clifford–Fourier transform preserves the
`L²` norm. -/
theorem integral_norm_sq_cliffordFourier
    (f : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n))) :
    ∫ ξ, ‖cliffordFourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [cliffordFourierIntegral_coe]
  exact integral_norm_sq_fourier f

/-! ### The inversion formula -/

/-- **Fourier inversion** for the Clifford–Fourier transform of Schwartz
functions: the inverse Clifford–Fourier transform recovers `f` from its
Clifford–Fourier transform. -/
theorem cliffordFourierInv_cliffordFourier
    (f : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n))) (x : EuclideanSpace ℝ (Fin n)) :
    cliffordFourierInvIntegral (cliffordFourierIntegral (⇑f)) x = f x := by
  have h : cliffordFourierIntegral (⇑f) = 𝓕 (⇑f) :=
    funext fun ξ => cliffordFourierIntegral_eq_fourier _ ξ
  rw [h, cliffordFourierInvIntegral_eq_fourierInv, ← fourier_coe, ← fourierInv_coe,
    FourierPair.fourierInv_fourier_eq f]

/-- **Fourier inversion** for the Clifford–Fourier transform of Schwartz
functions, the other composition. -/
theorem cliffordFourier_cliffordFourierInv
    (f : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n))) (x : EuclideanSpace ℝ (Fin n)) :
    cliffordFourierIntegral (cliffordFourierInvIntegral (⇑f)) x = f x := by
  have h : cliffordFourierInvIntegral (⇑f) = 𝓕⁻ (⇑f) :=
    funext fun ξ => cliffordFourierInvIntegral_eq_fourierInv _ ξ
  rw [h, cliffordFourierIntegral_eq_fourier, ← fourierInv_coe, ← fourier_coe,
    FourierInvPair.fourier_fourierInv_eq f]

/-! ### `L²` theory -/

/-- The Clifford–Fourier transform as a linear isometry equivalence of
`L²(ℝⁿ, Cl(n,0))` — the `L²` form of **Plancherel's theorem**. On Schwartz
functions it is given by `cliffordFourierIntegral`. -/
def cliffordFourierL2 :
    Lp (α := EuclideanSpace ℝ (Fin n)) (CliffordAlgebra (Q n)) 2 ≃ₗᵢ[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin n)) (CliffordAlgebra (Q n)) 2 :=
  Lp.fourierTransformₗᵢ _ _

@[simp] theorem norm_cliffordFourierL2_eq
    (f : Lp (α := EuclideanSpace ℝ (Fin n)) (CliffordAlgebra (Q n)) 2) :
    ‖cliffordFourierL2 f‖ = ‖f‖ :=
  cliffordFourierL2.norm_map f

@[simp] theorem cliffordFourierL2_symm_apply_apply
    (f : Lp (α := EuclideanSpace ℝ (Fin n)) (CliffordAlgebra (Q n)) 2) :
    cliffordFourierL2.symm (cliffordFourierL2 f) = f :=
  cliffordFourierL2.symm_apply_apply f

/-- On (the `L²` class of) a Schwartz function, `cliffordFourierL2` is computed
by the Clifford–Fourier integral. -/
theorem cliffordFourierL2_toLp (f : 𝓢(EuclideanSpace ℝ (Fin n), CliffordAlgebra (Q n))) :
    cliffordFourierL2 (f.toLp 2) = ((𝓕 f).toLp 2 :) :=
  SchwartzMap.toLp_fourier_eq f

end CliffordAlgebra.Euclidean
