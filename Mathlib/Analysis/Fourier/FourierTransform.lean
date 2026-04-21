/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

In namespace `VectorFourier`, we define the Fourier integral in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is a unitary additive character of `𝕜`, i.e. an `AddChar 𝕜 Circle`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, we define `fourierIntegral` to be the map from functions `V → E` to
functions `W → E` that sends `f` to

`fun w ↦ ∫ v in V, e (-L v w) • f v ∂μ`,

This includes the cases `W` is the dual of `V` and `L` is the canonical pairing, or `W = V` and `L`
is a bilinear form (e.g. an inner product).

In namespace `Fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `Real.fourierChar`, i.e. the character `fun x ↦ exp ((2 * π * x) * I)` (for which we
introduced the notation `𝐞` in the scope `FourierTransform`).

Another familiar case (which generalizes the previous one) is when `V = W` is an inner product space
over `ℝ` and `L` is the scalar product. We introduce two notations `𝓕` for the Fourier transform in
this case and `𝓕⁻ f (v) = 𝓕 f (-v)` for the inverse Fourier transform. These notations make
in particular sense for `V = W = ℝ`.

## Main results

At present the only nontrivial lemma we prove is `fourierIntegral_continuous`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

local notation "𝕊" => Circle

open MeasureTheory Filter

open scoped Topology

/-! ## Fourier theory for functions on general vector spaces -/

namespace VectorFourier

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

section Defs

/-- The Fourier transform integral for `f : V → E`, with respect to a bilinear form `L : V × W → 𝕜`
and an additive character `e`. -/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E)
    (w : W) : E :=
  ∫ v, e (-L v w) • f v ∂μ

theorem fourierIntegral_congr_ae (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
    {f₁ f₂ : V → E} (hf : f₁ =ᵐ[μ] f₂) : fourierIntegral e μ L f₁ = fourierIntegral e μ L f₂ := by
  ext
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (r : ℂ) :
    fourierIntegral e μ L (r • f) = r • fourierIntegral e μ L f := by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

/-- The uniform norm of the Fourier integral of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (w : W) :
    ‖fourierIntegral e μ L f w‖ ≤ ∫ v : V, ‖f v‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

/-- The Fourier integral converts right-translation into scalar multiplication by a phase factor. -/
theorem fourierIntegral_comp_add_right [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
    [μ.IsAddRightInvariant] (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (v₀ : V) :
    fourierIntegral e μ L (f ∘ fun v ↦ v + v₀) =
      fun w ↦ e (L v₀ w) • fourierIntegral e μ L f w := by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V ↦ (e (-L (v - v₀) w) : ℂ) • f v, ← integral_smul]
  congr 1 with v
  rw [← smul_assoc, smul_eq_mul, ← Circle.coe_mul, ← e.map_add_eq_mul, ← LinearMap.neg_apply,
    ← sub_eq_add_neg, ← LinearMap.sub_apply, map_sub, neg_sub]

end Defs

section Continuous

/-!
In this section we assume 𝕜, `V`, `W` have topologies,
and `L`, `e` are continuous (but `f` needn't be).

This is used to ensure that `e (-L v w)` is (a.e. strongly) measurable. We could get away with
imposing only a measurable-space structure on 𝕜 (it doesn't have to be the Borel sigma-algebra of
a topology); but it seems hard to imagine cases where this extra generality would be useful, and
allowing it would complicate matters in the most important use cases.
-/
variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- For any `w`, the Fourier integral is convergent iff `f` is integrable. -/
theorem fourierIntegral_convergent_iff (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (w : W) :
    Integrable (fun v : V ↦ e (-L v w) • f v) μ ↔ Integrable f μ := by
  -- first prove one-way implication
  have aux {g : V → E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V ↦ e (-L v x) • g v) μ := by
    have c : Continuous fun v ↦ e (-L v x) := he.comp (hL.comp (.prodMk_left _)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.smul hg.1), Circle.norm_smul]
    exact hg.norm
  -- then use it for both directions
  refine ⟨fun hf ↦ ?_, fun hf ↦ aux hf w⟩
  have := aux hf (-w)
  simp_rw [← mul_smul (e _) (e _) (f _), ← e.map_add_eq_mul, map_neg, neg_add_cancel,
    e.map_zero_eq_one, one_smul] at this -- the `(e _)` speeds up elaboration considerably
  exact this

theorem fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {f g : V → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral e μ L (f + g) = fourierIntegral e μ L f + fourierIntegral e μ L g := by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg

/-- The Fourier integral of an `L^1` function is a continuous function. -/
theorem fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w ↦ ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w ↦ ae_of_all _ fun v ↦ le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · filter_upwards with v
    fun_prop

end Continuous

section Fubini

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}
  {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν] [SecondCountableTopology V]

variable {σ : ℂ →+* ℂ} [RingHomIsometric σ]

/-- Fubini's theorem for the Fourier integral.

This is the main technical step in proving both Parseval's identity and self-adjointness of the
Fourier transform. -/
theorem integral_fourierIntegral_swap
    {f : V → E} {g : W → F} (M : F →L[ℂ] E →SL[σ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (∫ x, M (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν =
    ∫ x, (∫ ξ, M (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ := by
  rw [integral_integral_swap]
  have : Integrable (fun (p : W × V) ↦ ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
    (hg.norm.mul_prod hf.norm).const_mul _
  apply this.mono
  · change AEStronglyMeasurable (fun p : W × V ↦ (M (g p.1) (e (-(L p.2) p.1) • f p.2))) _
    have A : AEStronglyMeasurable (fun (p : W × V) ↦ e (-L p.2 p.1) • f p.2) (ν.prod μ) := by
      refine (Continuous.aestronglyMeasurable ?_).smul hf.1.comp_snd
      exact he.comp (hL.comp continuous_swap).neg
    have A' : AEStronglyMeasurable (fun p ↦ (g p.1, e (-(L p.2) p.1) • f p.2) : W × V → F × E)
      (Measure.prod ν μ) := hg.1.comp_fst.prodMk A
    have hM : Continuous (fun q ↦ M q.1 q.2 : F × E → G) :=
      -- There is no `Continuous.clm_apply` for semilinear continuous maps
      (M.flip.cont.comp continuous_snd).clm_apply continuous_fst
    apply hM.comp_aestronglyMeasurable A' -- `exact` works, but `apply` is 10x faster!
  · filter_upwards with ⟨ξ, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul, norm_norm, ge_iff_le, ← mul_assoc]
    convert M.le_opNorm₂ (g ξ) (e (-L x ξ) • f x) using 2
    simp

variable [CompleteSpace E] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierIntegral_eq_flip
    {f : V → E} {g : W → F} (M : E →L[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral_def, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (-L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, LinearMap.flip_apply]
  _ = ∫ x, M (f x) (∫ ξ, e (-L.flip ξ x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    apply (fourierIntegral_convergent_iff he _ _).2 hg
    exact hL.comp continuous_swap

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourierIntegral_smul_eq_flip
    {f : V → ℂ} {g : W → F} (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν =
      ∫ x, (f x) • (fourierIntegral e ν L.flip g x) ∂μ :=
  integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ) he hL hf hg

/-- The Fourier transform satisfies `∫ 𝓕 f * conj g = ∫ f * conj (𝓕⁻¹ g)`, which together
with the Fourier inversion theorem yields Plancherel's theorem. The stated version is more
convenient since it does only require integrability of `f` and `g`.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_sesq_fourierIntegral_eq_neg_flip
    {f : V → E} {g : W → F} (M : E →L⋆[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν (-L.flip) g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral_def, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    congr with x
    congr with ξ
    rw [← smul_one_smul ℂ _ (f x), ← smul_one_smul ℂ _ (g ξ)]
    simp only [map_smulₛₗ, ContinuousLinearMap.flip_apply, LinearMap.flip_apply, RingHom.id_apply,
      Circle.smul_def, smul_eq_mul, mul_one, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv,
      inv_inv]
  _ = ∫ x, (∫ ξ, M (f x) (e (-(-L.flip ξ) x) • g ξ) ∂ν) ∂μ := by
    simp only [LinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower, LinearMap.neg_apply,
      neg_neg]
  _ = ∫ x, M (f x) (∫ ξ, e (-(-L.flip ξ) x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    have hLflip : Continuous fun (p : W × V) => (-L.flip p.1) p.2 :=
      (continuous_neg.comp hL).comp continuous_swap
    exact (fourierIntegral_convergent_iff (L := -L.flip) he hLflip x).2 hg

end Fubini

lemma fourierIntegral_probChar {V W : Type*} {_ : MeasurableSpace V}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : Measure V) (f : V → E) (w : W) :
    fourierIntegral Real.probChar μ L f w =
      ∫ v : V, Complex.exp (- L v w * Complex.I) • f v ∂μ := by
  simp_rw [fourierIntegral, Circle.smul_def, Real.probChar_apply, Complex.ofReal_neg]

end VectorFourier

namespace VectorFourier

variable {𝕜 ι E F V W : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →L[𝕜] W →L[𝕜] 𝕜}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]

theorem fourierIntegral_continuousLinearMap_apply
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (he : Continuous e) (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w a =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x ↦ f x a) w := by
  rw [fourierIntegral, ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

theorem fourierIntegral_continuousMultilinearMap_apply
    {f : V → (ContinuousMultilinearMap ℝ M E)} {m : (i : ι) → M i} {w : W} (he : Continuous e)
    (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w m =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x ↦ f x m) w := by
  rw [fourierIntegral, ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

end VectorFourier


/-! ## Fourier theory for functions on `𝕜` -/


namespace Fourier

variable {𝕜 : Type*} [CommRing 𝕜] [MeasurableSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

section Defs

/-- The Fourier transform integral for `f : 𝕜 → E`, with respect to the measure `μ` and additive
character `e`. -/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E :=
  VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w

theorem fourierIntegral_def (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) :
    fourierIntegral e μ f w = ∫ v : 𝕜, e (-(v * w)) • f v ∂μ :=
  rfl

theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (r : ℂ) :
    fourierIntegral e μ (r • f) = r • fourierIntegral e μ f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    (f : 𝕜 → E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ ≤ ∫ x : 𝕜, ‖f x‖ ∂μ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The Fourier transform converts right-translation into scalar multiplication by a phase
factor. -/
theorem fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    [μ.IsAddRightInvariant] (f : 𝕜 → E) (v₀ : 𝕜) :
    fourierIntegral e μ (f ∘ fun v ↦ v + v₀) = fun w ↦ e (v₀ * w) • fourierIntegral e μ f w :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

end Defs

end Fourier

open scoped Real

namespace Real

open FourierTransform

variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral fourierChar μ L f w =
      ∫ v : V, Complex.exp (↑(-2 * π * L v w) * Complex.I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]

/-- The Fourier integral is well defined iff the function is integrable. Version with a general
continuous bilinear function `L`. For the specialization to the inner product in an inner product
space, see `Real.fourierIntegral_convergent_iff`. -/
@[simp]
theorem fourierIntegral_convergent_iff' {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V → E} (L : V →L[ℝ] W →L[ℝ] ℝ) (w : W) :
    Integrable (fun v : V ↦ 𝐞 (- L v w) • f v) μ ↔ Integrable f μ :=
  VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₁₂)
    continuous_fourierChar L.continuous₂ _

section Apply

variable {ι F V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure V} {L : V →L[ℝ] W →L[ℝ] ℝ}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]

theorem fourierIntegral_continuousLinearMap_apply'
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w a =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x ↦ f x a) w :=
  VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf

theorem fourierIntegral_continuousMultilinearMap_apply'
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w m =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x ↦ f x m) w :=
  VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf

end Apply

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W]

open scoped RealInnerProductSpace

@[simp] theorem fourierIntegral_convergent_iff {μ : Measure V} {f : V → E} (w : V) :
    Integrable (fun v : V ↦ 𝐞 (- ⟪v, w⟫) • f v) μ ↔ Integrable f μ :=
  fourierIntegral_convergent_iff' (innerSL ℝ) w

variable [FiniteDimensional ℝ V]

instance instFourierTransform : FourierTransform (V → E) (V → E) where
  fourier f := VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f

instance instFourierTransformInv : FourierTransformInv (V → E) (V → E) where
  fourierInv f w := VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w

@[deprecated (since := "2025-11-12")]
alias fourierIntegral := FourierTransform.fourier

@[deprecated (since := "2025-11-12")]
alias fourierIntegralInv := FourierTransform.fourierInv

lemma fourier_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v := rfl

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_eq := fourier_eq

lemma fourier_eq' (f : V → E) (w : V) :
    𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourier_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_eq' := fourier_eq'

theorem fourier_congr_ae {f₁ f₂ : V → E} (hf : f₁ =ᵐ[volume] f₂) (x : V) : 𝓕 f₁ x = 𝓕 f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

lemma fourierInv_eq (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v := by
  simp [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral]

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_eq := fourierInv_eq

lemma fourierInv_eq' (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierInv_eq, Circle.smul_def, Real.fourierChar_apply]

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_eq' := fourierInv_eq'

lemma fourier_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕 (f ∘ A) w = (𝓕 f) (A w) := by
  simp only [fourier_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_comp_linearIsometry := fourier_comp_linearIsometry

lemma fourierInv_eq_fourier_neg (f : V → E) (w : V) :
    𝓕⁻ f w = 𝓕 f (-w) := by
  simp [fourier_eq, fourierInv_eq]

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_eq_fourierIntegral_neg := fourierInv_eq_fourier_neg

lemma fourierInv_eq_fourier_comp_neg (f : V → E) :
    𝓕⁻ f = 𝓕 (fun x ↦ f (-x)) := by
  ext y
  rw [fourierInv_eq_fourier_neg]
  change 𝓕 f (LinearIsometryEquiv.neg ℝ y) = 𝓕 (f ∘ LinearIsometryEquiv.neg ℝ) y
  exact (fourier_comp_linearIsometry _ _ _).symm

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_eq_fourierIntegral_comp_neg := fourierInv_eq_fourier_comp_neg

lemma fourierInv_comm (f : V → E) :
    𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f) := by
  conv_rhs => rw [fourierInv_eq_fourier_comp_neg]
  simp_rw [← fourierInv_eq_fourier_neg]

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_comm := fourierInv_comm

lemma fourierInv_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w) := by
  simp [fourierInv_eq_fourier_neg, fourier_comp_linearIsometry]

@[deprecated (since := "2025-11-16")]
alias fourierIntegralInv_comp_linearIsometry := fourierInv_comp_linearIsometry

theorem fourier_real_eq (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, 𝐞 (-(v * w)) • f v := by
  simp_rw [mul_comm _ w]
  rfl

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_real_eq := fourier_real_eq

theorem fourier_real_eq_integral_exp_smul (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourier_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_real_eq_integral_exp_smul := fourier_real_eq_integral_exp_smul

theorem fourier_continuousLinearMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → (F →L[ℝ] E)} {a : F} {v : V} (hf : Integrable f) :
    𝓕 f v a = 𝓕 (fun x ↦ f x a) v :=
  fourierIntegral_continuousLinearMap_apply' (L := innerSL ℝ) hf

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_continuousLinearMap_apply := fourier_continuousLinearMap_apply

theorem fourier_continuousMultilinearMap_apply {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {v : V} (hf : Integrable f) :
    𝓕 f v m = 𝓕 (fun x ↦ f x m) v :=
  fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) hf

@[deprecated (since := "2025-11-16")]
alias fourierIntegral_continuousMultilinearMap_apply := fourier_continuousMultilinearMap_apply

open scoped BoundedContinuousFunction

/-- The Fourier transform from `L1` functions to bounded continuous functions. -/
def Lp.fourierTransform (f : Lp (α := V) E 1) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V → E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (L1.integrable_coeFn f))
  ‖f‖ fun x ↦ by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le

@[norm_cast]
theorem Lp.coe_fourierTransform (f : Lp (α := V) E 1) :
    (Lp.fourierTransform f : V → E) = 𝓕 (f : V → E) := rfl

@[simp]
theorem Lp.fourierTransform_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransform f x = 𝓕 (f : V → E) x := rfl

@[simp]
theorem fourierTransform_toLp {f : V → E} (hf : MemLp f 1) :
    (Lp.fourierTransform hf.toLp : V → E) = 𝓕 f := by
  simp only [Lp.coe_fourierTransform]
  ext x
  exact (Real.fourier_congr_ae hf.coeFn_toLp) x

variable (V E) in
/-- The Fourier transform from `L1` functions to bounded continuous functions as a continuous linear
map. -/
def Lp.fourierTransformCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  LinearMap.mkContinuous
    { toFun := Lp.fourierTransform
      map_add' f g := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
          Real.fourier_eq]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with x h₁
          rw [h₁]
          simp
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn f
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn g
      map_smul' c f := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_smul, Real.fourier_eq]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x h
        rw [h, smul_comm]
        simp }
    1 fun f ↦ by
      rw [one_mul, BoundedContinuousFunction.norm_le (by positivity)]
      intro x
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.fourierTransform_apply, Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans
      simp_rw [Circle.norm_smul]
      exact (L1.norm_eq_integral_norm f).symm.le

@[simp]
theorem Lp.fourierTransformCLM_apply (f : Lp (α := V) E 1) :
  Lp.fourierTransformCLM V E f = Lp.fourierTransform f := rfl

end Real
