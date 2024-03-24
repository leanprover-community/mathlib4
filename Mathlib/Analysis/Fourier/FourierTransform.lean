/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

In namespace `Fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `Real.fourierChar`, i.e. the character `fun x ↦ exp ((2 * π * x) * I)` (for which we
introduce the notation `𝐞` in the locale `FourierTransform`).

Another familiar case (which generalizes the previous one) is when `V = W` is an inner product space
over `ℝ` and `L` is the scalar product. We introduce two notations `𝓕` for the Fourier transform in
this case and `𝓕⁻ f (v) = 𝓕 f (-v)` for the inverse Fourier transform. These notations make
in particular sense for `V = W = ℝ`.

## Main results

At present the only nontrivial lemma we prove is `fourierIntegral_continuous`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/


noncomputable section

local notation "𝕊" => circle

open MeasureTheory Filter

open scoped Topology

-- To avoid messing around with multiplicative vs. additive characters, we make a notation.
/-- Notation for multiplicative character applied in an additive setting. -/
scoped[FourierTransform] notation e "[" x "]" => (e (Multiplicative.ofAdd x) : ℂ)

open FourierTransform

/-! ## Fourier theory for functions on general vector spaces -/


namespace VectorFourier

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

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
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V => e[-L (v - v₀) w] • f v, ← integral_smul]
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
theorem fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) {f : V → E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w => ((fourier_integral_convergent_iff he hL w).mp hf).1
  · refine' fun w => ae_of_all _ fun v => _
    · rw [norm_smul, Complex.norm_eq_abs, abs_coe_circle, one_mul]
  · exact hf.norm
  · rw [continuous_induced_rng] at he
    refine' ae_of_all _ fun v => (he.comp (continuous_ofAdd.comp _)).smul continuous_const
    exact (hL.comp (continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩)).neg
#align vector_fourier.fourier_integral_continuous VectorFourier.fourierIntegral_continuous

end Continuous

section Fubini

variable [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
  {e : Multiplicative 𝕜 →* 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}
  {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν] [SecondCountableTopology V]

variable [CompleteSpace E] [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.
Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierIntegral_eq_flip
    {f : V → E} {g : W → F} (M : E →L[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν
    = ∫ ξ, M.flip (g ξ) (∫ x, e[-L x ξ] • f x ∂μ) ∂ν := rfl
  _ = ∫ ξ, (∫ x, M.flip (g ξ) (e[-L x ξ] • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourier_integral_convergent_iff he hL _).1 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e[-L x ξ] • f x) ∂ν) ∂μ := by
    rw [integral_integral_swap]
    have : Integrable (fun (p : W × V) ↦ ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
      (hg.norm.prod_mul hf.norm).const_mul _
    apply this.mono
    · have A : AEStronglyMeasurable (fun (p : W × V) ↦ e[-L p.2 p.1] • f p.2) (ν.prod μ) := by
        apply (Continuous.aestronglyMeasurable ?_).smul hf.1.snd
        refine (continuous_induced_rng.mp he).comp (continuous_ofAdd.comp ?_)
        exact (hL.comp continuous_swap).neg
      exact M.flip.continuous₂.comp_aestronglyMeasurable (hg.1.fst.prod_mk A)
    · apply eventually_of_forall
      rintro ⟨ξ, x⟩
      simp only [ofAdd_neg, map_inv, coe_inv_unitSphere, _root_.map_smul,
        ContinuousLinearMap.flip_apply, Function.uncurry_apply_pair, norm_smul, norm_inv,
        norm_eq_of_mem_sphere, inv_one, one_mul, norm_mul, norm_norm]
      exact (M.le_opNorm₂ (f x) (g ξ)).trans (le_of_eq (by ring))
  _ = ∫ x, (∫ ξ, M (f x) (e[-L.flip ξ x] • g ξ) ∂ν) ∂μ := by simp
  _ = ∫ x, M (f x) (∫ ξ, e[-L.flip ξ x] • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    apply (fourier_integral_convergent_iff he _ _).1 hg
    exact hL.comp continuous_swap

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourierIntegral_smul_eq_flip
    {f : V → ℂ} {g : W → F} (he : Continuous e)
    (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν =
      ∫ x, (f x) • (fourierIntegral e ν L.flip g x) ∂μ :=
  integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ) he hL hf hg

end Fubini

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

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar

theorem fourierChar_apply (x : ℝ) : 𝐞[x] = Complex.exp (↑(2 * π * x) * Complex.I) :=
  by rfl
#align real.fourier_char_apply Real.fourierChar_apply

@[continuity]
theorem continuous_fourierChar : Continuous 𝐞 :=
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


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  {W : Type*} [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W]

open scoped RealInnerProductSpace

/-- The Fourier transform of a function on an inner product space, with respect to the standard
additive character `ω ↦ exp (2 i π ω)`. -/
def fourierIntegral (f : V → E) (w : V) : E :=
  VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f w
#align real.fourier_integral Real.fourierIntegral

/-- The inverse Fourier transform of a function on an inner product space, defined as the Fourier
transform but with opposite sign in the exponential. -/
def fourierIntegralInv (f : V → E) (w : V) : E :=
  VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w

@[inherit_doc] scoped[FourierTransform] notation "𝓕" => Real.fourierIntegral
@[inherit_doc] scoped[FourierTransform] notation "𝓕⁻" => Real.fourierIntegralInv

lemma fourierIntegral_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, 𝐞[-⟪v, w⟫] • f v := rfl

lemma fourierIntegral_eq' (f : V → E) (w : V) :
    𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierIntegral_eq, Real.fourierChar_apply, mul_neg, neg_mul]

lemma fourierIntegralInv_eq (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, 𝐞[⟪v, w⟫] • f v := by
  simp [fourierIntegralInv, VectorFourier.fourierIntegral]

lemma fourierIntegralInv_eq' (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierIntegralInv_eq, Real.fourierChar_apply]

lemma fourierIntegralInv_eq_fourierIntegral_neg (f : V → E) (w : V) :
    𝓕⁻ f w = 𝓕 f (-w) := by
  simp [fourierIntegral_eq, fourierIntegralInv_eq]

lemma fourierIntegral_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕 (f ∘ A) w = (𝓕 f) (A w) := by
  simp only [fourierIntegral_eq, ofAdd_neg, map_inv, coe_inv_unitSphere, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding,
    ← A.inner_map_map]

lemma fourierIntegralInv_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w) := by
  simp [fourierIntegralInv_eq_fourierIntegral_neg, fourierIntegral_comp_linearIsometry]

theorem fourierIntegral_real_eq (f : ℝ → E) (w : ℝ) :
    fourierIntegral f w = ∫ v : ℝ, 𝐞[-(v * w)] • f v :=
  rfl
#align real.fourier_integral_def Real.fourierIntegral_real_eq

@[deprecated] alias fourierIntegral_def := fourierIntegral_real_eq -- deprecated on 2024-02-21

theorem fourierIntegral_real_eq_integral_exp_smul (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourierIntegral_real_eq, Real.fourierChar_apply, mul_neg, neg_mul, mul_assoc]
#align real.fourier_integral_eq_integral_exp_smul Real.fourierIntegral_real_eq_integral_exp_smul

@[deprecated] alias fourierIntegral_eq_integral_exp_smul :=
  fourierIntegral_real_eq_integral_exp_smul -- deprecated on 2024-02-21

end Real
