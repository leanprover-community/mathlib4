/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Group.Integration
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

#align_import analysis.fourier.fourier_transform from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

In namespace `VectorFourier`, we define the Fourier integral in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is a unitary additive character of `𝕜`, i.e. a homomorphism `(Multiplicative 𝕜) →* circle`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, we define `fourierIntegral` to be the map from functions `V → E` to
functions `W → E` that sends `f` to

`fun w ↦ ∫ v in V, e [-L v w] • f v ∂μ`,

where `e [x]` is notational sugar for `(e (Multiplicative.ofAdd x) : ℂ)` (available in locale
`fourier_transform`). This includes the cases `W` is the dual of `V` and `L` is the canonical
pairing, or `W = V` and `L` is a bilinear form (e.g. an inner product).

In namespace `fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `Real.fourierChar`, i.e. the character `fun x ↦ exp ((2 * π * x) * I)`. The Fourier integral
in this case is defined as `Real.fourierIntegral`.

## Main results

At present the only nontrivial lemma we prove is `fourierIntegral_continuous`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/


noncomputable section

local notation "𝕊" => circle

open MeasureTheory Filter

open scoped Topology

-- To avoid messing around with multiplicative vs. additive characters, we make a notation.
scoped[FourierTransform] notation e "[" x "]" => (e (Multiplicative.ofAdd x) : ℂ)

open FourierTransform

/-! ## Fourier theory for functions on general vector spaces -/


namespace VectorFourier

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Defs

/-- The Fourier transform integral for `f : V → E`, with respect to a bilinear form `L : V × W → 𝕜`
and an additive character `e`. -/
def fourierIntegral (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E)
    (w : W) : E :=
  ∫ v, e[-L v w] • f v ∂μ
#align vector_fourier.fourier_integral VectorFourier.fourierIntegral

theorem fourierIntegral_smul_const (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (r : ℂ) :
    fourierIntegral e μ L (r • f) = r • fourierIntegral e μ L f := by
  ext1 w
  -- Porting note: was
  -- simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]
  simp only [Pi.smul_apply, fourierIntegral, ← integral_smul]
  congr; funext
  rw [smul_comm]
#align vector_fourier.fourier_integral_smul_const VectorFourier.fourierIntegral_smul_const

/-- The uniform norm of the Fourier integral of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (w : W) :
    ‖fourierIntegral e μ L f w‖ ≤ ∫ v : V, ‖f v‖ ∂μ := by
  refine' (norm_integral_le_integral_norm _).trans (le_of_eq _)
  simp_rw [norm_smul, Complex.norm_eq_abs, abs_coe_circle, one_mul]
#align vector_fourier.norm_fourier_integral_le_integral_norm VectorFourier.norm_fourierIntegral_le_integral_norm

/-- The Fourier integral converts right-translation into scalar multiplication by a phase factor.-/
theorem fourierIntegral_comp_add_right [MeasurableAdd V] (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure V)
    [μ.IsAddRightInvariant] (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (v₀ : V) :
    fourierIntegral e μ L (f ∘ fun v => v + v₀) =
      fun w => e[L v₀ w] • fourierIntegral e μ L f w := by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply]
  conv in L _ => rw [← add_sub_cancel v v₀]
  rw [integral_add_right_eq_self fun v : V => e[-L (v - v₀) w] • f v]
  dsimp only
  rw [← integral_smul]
  congr 1 with v
  rw [← smul_assoc, smul_eq_mul, ← Submonoid.coe_mul, ← e.map_mul, ← ofAdd_add, ←
    LinearMap.neg_apply, ← sub_eq_add_neg, ← LinearMap.sub_apply, LinearMap.map_sub, neg_sub]
#align vector_fourier.fourier_integral_comp_add_right VectorFourier.fourierIntegral_comp_add_right

end Defs

section Continuous

/- In this section we assume 𝕜, V, W have topologies, and L, e are continuous (but f needn't be).
   This is used to ensure that `e [-L v w]` is (ae strongly) measurable. We could get away with
   imposing only a measurable-space structure on 𝕜 (it doesn't have to be the Borel sigma-algebra of
   a topology); but it seems hard to imagine cases where this extra generality would be useful, and
   allowing it would complicate matters in the most important use cases.
-/
variable [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : Multiplicative 𝕜 →* 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- For any `w`, the Fourier integral is convergent iff `f` is integrable. -/
theorem fourier_integral_convergent_iff (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) {f : V → E} (w : W) :
    Integrable f μ ↔ Integrable (fun v : V => e[-L v w] • f v) μ := by
  -- first prove one-way implication
  have aux :
    ∀ {g : V → E} (_ : Integrable g μ) (x : W), Integrable (fun v : V => e[-L v x] • g v) μ := by
    intro g hg x
    have c : Continuous fun v => e[-L v x] := by
      refine' (continuous_induced_rng.mp he).comp (continuous_ofAdd.comp (Continuous.neg _))
      exact hL.comp (continuous_prod_mk.mpr ⟨continuous_id, continuous_const⟩)
    rw [← integrable_norm_iff (c.aestronglyMeasurable.smul hg.1)]
    convert hg.norm using 2
    rw [norm_smul, Complex.norm_eq_abs, abs_coe_circle, one_mul]
  -- then use it for both directions
  refine' ⟨fun hf => aux hf w, fun hf => _⟩
  convert aux hf (-w)
  rw [← smul_assoc, smul_eq_mul, ← Submonoid.coe_mul, ← MonoidHom.map_mul, ← ofAdd_add,
    LinearMap.map_neg, neg_neg, ← sub_eq_add_neg, sub_self, ofAdd_zero, MonoidHom.map_one,
    Submonoid.coe_one, one_smul]
#align vector_fourier.fourier_integral_convergent_iff VectorFourier.fourier_integral_convergent_iff

variable [CompleteSpace E]

theorem fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2)
    {f g : V → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral e μ L f + fourierIntegral e μ L g = fourierIntegral e μ L (f + g) := by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourier_integral_convergent_iff he hL w).mp hf
  · exact (fourier_integral_convergent_iff he hL w).mp hg
#align vector_fourier.fourier_integral_add VectorFourier.fourierIntegral_add

/-- The Fourier integral of an `L^1` function is a continuous function. -/
theorem fourierIntegral_continuous [TopologicalSpace.FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) {f : V → E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w => ((fourier_integral_convergent_iff he hL w).mp hf).1
  · refine' fun w => ae_of_all _ fun v => _
    · exact fun v => ‖f v‖
    · rw [norm_smul, Complex.norm_eq_abs, abs_coe_circle, one_mul]
  · exact hf.norm
  · rw [continuous_induced_rng] at he
    refine' ae_of_all _ fun v => (he.comp (continuous_ofAdd.comp _)).smul continuous_const
    refine' (hL.comp (continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩)).neg
#align vector_fourier.fourier_integral_continuous VectorFourier.fourierIntegral_continuous

end Continuous

end VectorFourier

/-! ## Fourier theory for functions on `𝕜` -/


namespace Fourier

variable {𝕜 : Type*} [CommRing 𝕜] [MeasurableSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

section Defs

variable [CompleteSpace E]

/-- The Fourier transform integral for `f : 𝕜 → E`, with respect to the measure `μ` and additive
character `e`. -/
def fourierIntegral (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E :=
  VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w
#align fourier.fourier_integral Fourier.fourierIntegral

theorem fourierIntegral_def (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) :
    fourierIntegral e μ f w = ∫ v : 𝕜, e[-(v * w)] • f v ∂μ :=
  rfl
#align fourier.fourier_integral_def Fourier.fourierIntegral_def

theorem fourierIntegral_smul_const (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (r : ℂ) :
    fourierIntegral e μ (r • f) = r • fourierIntegral e μ f :=
  VectorFourier.fourierIntegral_smul_const _ _ _ _ _
#align fourier.fourier_integral_smul_const Fourier.fourierIntegral_smul_const

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure 𝕜)
    (f : 𝕜 → E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ ≤ ∫ x : 𝕜, ‖f x‖ ∂μ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
#align fourier.norm_fourier_integral_le_integral_norm Fourier.norm_fourierIntegral_le_integral_norm

/-- The Fourier transform converts right-translation into scalar multiplication by a phase factor.-/
theorem fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : Multiplicative 𝕜 →* 𝕊) (μ : Measure 𝕜)
    [μ.IsAddRightInvariant] (f : 𝕜 → E) (v₀ : 𝕜) :
    fourierIntegral e μ (f ∘ fun v => v + v₀) = fun w => e[v₀ * w] • fourierIntegral e μ f w :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _
#align fourier.fourier_integral_comp_add_right Fourier.fourierIntegral_comp_add_right

end Defs

end Fourier

open scoped Real

namespace Real

/-- The standard additive character of `ℝ`, given by `fun x ↦ exp (2 * π * x * I)`. -/
def fourierChar : Multiplicative ℝ →* 𝕊 where
  toFun z := expMapCircle (2 * π * Multiplicative.toAdd z)
  map_one' := by simp only; rw [toAdd_one, mul_zero, expMapCircle_zero]
  map_mul' x y := by simp only; rw [toAdd_mul, mul_add, expMapCircle_add]
#align real.fourier_char Real.fourierChar

theorem fourierChar_apply (x : ℝ) : Real.fourierChar[x] = Complex.exp (↑(2 * π * x) * Complex.I) :=
  by rfl
#align real.fourier_char_apply Real.fourierChar_apply

@[continuity]
theorem continuous_fourierChar : Continuous Real.fourierChar :=
  (map_continuous expMapCircle).comp (continuous_const.mul continuous_toAdd)
#align real.continuous_fourier_char Real.continuous_fourierChar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral fourierChar μ L f w =
      ∫ v : V, Complex.exp (↑(-2 * π * L v w) * Complex.I) • f v ∂μ :=
  by simp_rw [VectorFourier.fourierIntegral, Real.fourierChar_apply, mul_neg, neg_mul]
#align real.vector_fourier_integral_eq_integral_exp_smul Real.vector_fourierIntegral_eq_integral_exp_smul

/-- The Fourier integral for `f : ℝ → E`, with respect to the standard additive character and
measure on `ℝ`. -/
def fourierIntegral (f : ℝ → E) (w : ℝ) :=
  Fourier.fourierIntegral fourierChar volume f w
#align real.fourier_integral Real.fourierIntegral

theorem fourierIntegral_def (f : ℝ → E) (w : ℝ) :
    fourierIntegral f w = ∫ v : ℝ, fourierChar[-(v * w)] • f v :=
  rfl
#align real.fourier_integral_def Real.fourierIntegral_def

scoped[FourierTransform] notation "𝓕" => Real.fourierIntegral

theorem fourierIntegral_eq_integral_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourierIntegral_def, Real.fourierChar_apply, mul_neg, neg_mul, mul_assoc]
#align real.fourier_integral_eq_integral_exp_smul Real.fourierIntegral_eq_integral_exp_smul

end Real
