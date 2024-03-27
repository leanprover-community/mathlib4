/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
/-!
# Derivative of the Fourier transform

In this file we compute the Fréchet derivative of `𝓕 f`, where `f` is a function such that both
`f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here `𝓕` is understood as an operator `(V → E) → (W → E)`,
where `V` and `W` are normed `ℝ`-vector spaces and the Fourier transform is taken with respect to a
continuous `ℝ`-bilinear pairing `L : V × W → ℝ`.

We also give a separate lemma for the most common case when `V = W = ℝ` and `L` is the obvious
multiplication map.
-/

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology

lemma Real.hasDerivAt_fourierChar (x : ℝ) : HasDerivAt (𝐞 · : ℝ → ℂ) (2 * π * I * 𝐞 x) x := by
  have h1 (y : ℝ) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type uE} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v ↦ (w ↦ -2 * π * I * L(v, w) • f v)`. -/
def mul_L (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)

/-- The `w`-derivative of the Fourier transform integrand. -/
lemma hasFDerivAt_fourier_transform_integrand_right (v : V) (w : W) :
    HasFDerivAt (fun w' ↦ 𝐞 (-L v w') • f v) (𝐞 (-L v w) • mul_L L f v) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext1 w'
  simp_rw [mul_L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, Submonoid.smul_def, smul_eq_mul]
  push_cast
  ring_nf

/-- Norm of the `w`-derivative of the Fourier transform integrand. -/
lemma norm_fderiv_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖𝐞 (-L v w) • mul_L L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := by
  rw [norm_circle_smul, mul_L, norm_smul, norm_neg, norm_mul, norm_mul, norm_eq_abs I, abs_I,
    mul_one, norm_eq_abs ((_ : ℝ) : ℂ), Complex.abs_of_nonneg pi_pos.le, norm_eq_abs (2 : ℂ),
    Complex.abs_two, ContinuousLinearMap.norm_smulRight_apply, ← mul_assoc]

lemma norm_fderiv_fourier_transform_integrand_right_le (v : V) (w : W) :
    ‖𝐞 (-L v w) • (mul_L L f v)‖ ≤ (2 * π) * ‖L‖ * ‖v‖ * ‖f v‖ := by
  rw [norm_fderiv_fourier_transform_integrand_right]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  conv_rhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (L.le_opNorm _) two_pi_pos.le

variable {f}

/-- Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and its derivative is
the Fourier transform of `mul_L L f`. -/
theorem hasFDerivAt_fourier [CompleteSpace E] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)]
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f)
      (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (mul_L L f) w) w := by
  let F : W → V → E := fun w' v ↦ 𝐞 (-L v w') • f v
  let F' : W → V → W →L[ℝ] E := fun w' v ↦ 𝐞 (-L v w') • mul_L L f v
  let B : V → ℝ := fun v ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (VectorFourier.fourier_integral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₂ p.1 p.2)) w').mp hf
  have h1 : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    eventually_of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .smul ?_ ?_
    · refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
      exact (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
    · apply AEStronglyMeasurable.const_smul'
      have aux0 : Continuous fun p : (W →L[ℝ] ℝ) × E ↦ p.1.smulRight p.2 :=
        (ContinuousLinearMap.smulRightL ℝ W E).continuous₂
      have aux1 : AEStronglyMeasurable (fun v ↦ (L v, f v)) μ :=
        L.continuous.aestronglyMeasurable.prod_mk hf.1
      apply aux0.comp_aestronglyMeasurable aux1
  have h4 : (∀ᵐ v ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v) := by
    filter_upwards with v w' _
    exact norm_fderiv_fourier_transform_integrand_right_le L f v w'
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ v ∂μ, ∀ w', w' ∈ Metric.ball w 1 → HasFDerivAt (fun x ↦ F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ ↦ hasFDerivAt_fourier_transform_integrand_right L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le one_pos h1 (h0 w) h3 h4 h5 h6

/-- Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and its derivative is
the Fourier transform of `mul_L L f`. -/
theorem glouk [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] (n : ℕ)
    (hf : ∀ k ≤ n, Integrable (fun v ↦ ‖v‖^k * ‖f v‖) μ) (h'f : AEStronglyMeasurable f μ) :
    ContDiff ℝ n (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f) := by
  by_cases hE : CompleteSpace E; swap
  · have : VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f = 0 := by
      ext x; simp [VectorFourier.fourierIntegral, integral, hE]
    simpa [this] using contDiff_const
  induction n generalizing f E with
  | zero =>
    simp only [Nat.zero_eq, CharP.cast_eq_zero, contDiff_zero]
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    apply (integrable_norm_iff h'f).1
    simpa using hf _ le_rfl
  | succ n ih =>
    have A : AEStronglyMeasurable (mul_L L f) μ := by
      apply (AEStronglyMeasurable.const_smul' _ _)
      apply (ContinuousLinearMap.smulRightL ℝ W E).continuous₂.comp_aestronglyMeasurable
        (L.continuous.aestronglyMeasurable.prod_mk h'f)
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (mul_L L f), ?_, fun w ↦ ?_⟩
    · apply ih (fun k hk ↦ ?_) A (by infer_instance)
      apply Integrable.mono' ((hf (k + 1) (Nat.add_le_add_right hk 1)).const_mul (2 * π * ‖L‖))
      · exact (continuous_norm.aestronglyMeasurable.pow _).mul A.norm
      · filter_upwards with v
        calc
        ‖‖v‖ ^ k * ‖mul_L L f v‖‖
          = ‖v‖ ^ k * (2 * π * (‖L v‖ * ‖f v‖)) := by
          simp [mul_L, norm_smul, _root_.abs_of_nonneg pi_nonneg]
        _ ≤ ‖v‖ ^ k * (2 * π * ((‖L‖ * ‖v‖) * ‖f v‖)) := by gcongr; exact L.le_opNorm v
        _ = 2 * π * ‖L‖ * (‖v‖ ^ (k + 1) * ‖f v‖) := by rw [pow_succ]; ring
    · apply hasFDerivAt_fourier
      · apply (integrable_norm_iff h'f).1
        simpa using hf 0 bot_le
      · simpa using hf 1 (Nat.le_add_left 1 n)

/-- The formal multilinear series whose `n`-th term is
`(w₁, ..., wₙ) ↦ (-2Iπ)^n * L v w₁ * ... * L v wₙ • f v`.

For good continuity and differentiability properties, we decompose it as follows:
* Let `B` be the bilinear form mapping `u : W [×n]→L[ℝ] ℝ` and `m : E`
    to `u.smulRight m : W [×n]→L[ℝ] E`.
* We write the desired form as `(-2Iπ)^n • B (A v) (f v)` where `A` maps `(w₁, ..., wₙ)`
  to `L v w₁ * ... * L v wₙ`.
* To write `A`, consider the product of `n` terms, as a continuous multilinear
  map `J : ℝ [×n]→L[ℝ] ℝ`, and compose it with the linear maps `(L v ⬝, ..., L v ⬝)`. The map
  `(L₁, ..., Lₙ) ↦ J ∘ (L₁, ..., Lₙ)` is itself a continuous multilinear map from
  `(W →L[ℝ] ℝ)^n` to `W [×n]→L[ℝ] ℝ` that we denote by `C`.
  Then `A = C ∘ (fun v ↦ (L v ⬝, ..., L v ⬝))`, and is therefore continuous.

Here are the Lean names of the above maps:
* `B` is `smulRightL`
* `J` is `mkPiAlgebra ℝ (Fin n) ℝ`
* `C` is `compContinuousLinearMapLRight`.

-/
def bloublou (f : V → E) (v : V) : FormalMultilinearSeries ℝ W E := fun n ↦
  (- (2 * π * I))^n • ((ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (f v)).compContinuousLinearMap
  (fun _i ↦ L v))

open scoped BigOperators

@[simp] lemma bloublou_apply {f : V → E} {v : V} {n : ℕ} {m : Fin n → W} :
    bloublou L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v := by
  simp [bloublou]

open ContinuousMultilinearMap

lemma bloublou_eq_comp {f : V → E} {v : V} {n : ℕ} :
    bloublou L f v n = (- (2 * π * I))^n • smulRightL ℝ (fun (_ : Fin n) ↦ W) E
      (compContinuousLinearMapLRight
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ) (fun _ ↦ L v))
      (f v) := rfl

lemma continuous_bloublou {f : V → E} (hf : Continuous f) (n : ℕ) :
    Continuous (fun v ↦ bloublou L f v n) := by
  simp_rw [bloublou_eq_comp]
  apply Continuous.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _i ↦ L.continuous))




def bloublou_gnou (f : V → E) (v : V) (n : ℕ) (m : Fin n → W) :
      ∀ (i : Fin n ⊕ Unit), ContinuousMultilinearMap.SumProdUliftRingSpace ℝ E (Fin n) i
  | Sum.inl i => ULift.up (L v (m i))
  | Sum.inr _ => f v

lemma bloublou_apply' {f : V → E} {v : V} {n : ℕ} {m : Fin n → W} :
  bloublou L f v n m = (- (2 * π * I))^n •
    ((ContinuousMultilinearMap.mkPiRingSmul (ι := Fin n) ℝ E) (bloublou_gnou L f v n m)) := by
  have A (x : ULift.{uE} ℝ) : x.down = ULift.ringEquiv x := rfl
  simp [bloublou_gnou, A]
  rfl

lemma norm_bloublou_le (f : V → E) (v : V) (n : ℕ) :
    ‖bloublou L f v n‖ ≤ (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound _ (by positivity) (fun m ↦ ?_)
  calc
  ‖bloublou L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [_root_.abs_of_nonneg pi_nonneg, norm_smul]
  _ ≤ (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      · exact fun i _hi ↦ abs_nonneg _
      · exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

def bloublou_fourier [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)]
    (f : V → E) (w : W) : FormalMultilinearSeries ℝ W E := fun n ↦
  VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ bloublou L f v n) w

variable {L}

#check ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear

lemma aestronglyMeasurable_boublou [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V → E} {k : ℕ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v ↦ bloublou L f v k) μ := by
  simp_rw [bloublou_eq_comp]
  apply AEStronglyMeasurable.const_smul'
  apply Continuous.comp_aestronglyMeasurable₂
  let F : V → E → (W [×k]→L[ℝ] E) := fun v z ↦
    ((ContinuousMultilinearMap.mkPiRing ℝ (Fin k) z).compContinuousLinearMap
    (fun _i ↦ L v))
  change AEStronglyMeasurable (F.uncurry ∘ (fun v ↦ (v, f v))) μ
  have A : Continuous F.uncurry := by
    simp [F]
    sorry
  apply A.comp_aestronglyMeasurable
  exact aestronglyMeasurable_id.prod_mk hf


#exit

lemma integrable_bloublou [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V → E} {k : ℕ} (hf : Integrable (fun v ↦ ‖v‖^k * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) : Integrable (fun v ↦ bloublou L f v k) μ := by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ k)).mono' (aestronglyMeasurable_boublou h'f) ?_
  filter_upwards with v
  apply (norm_bloublou_le L f v k).trans (le_of_eq ?_)
  rw [mul_assoc]

lemma truc [CompleteSpace E] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] (n : ℕ∞)
    (hf : ∀ (k : ℕ), k ≤ n → Integrable (fun v ↦ ‖v‖^k * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo n (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f)
    (fun w n ↦ VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ bloublou L f v n) w) := by
  constructor
  · sorry /-intro w
    simp only [ContinuousMultilinearMap.uncurry0_apply, Matrix.zero_empty, fourierIntegral]
    rw [ContinuousMultilinearMap.integral_apply]
    · simp only [bloublou, pow_zero, one_smul, ContinuousMultilinearMap.smul_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiRing_apply, Finset.univ_eq_empty, Finset.prod_empty]
    · apply (hf 0 bot_le).mono'
      · apply AEStronglyMeasurable.smul _ (aestronglyMeasurable_boublou h'f)
        apply Continuous.aestronglyMeasurable
        apply Real.continuous_fourierChar.comp (by continuity)
      · filter_upwards with v
        simp only [bloublou, pow_zero, one_smul, norm_circle_smul, one_mul]
        exact ContinuousMultilinearMap.opNorm_le_bound _ (norm_nonneg _) (fun m ↦ by simp) -/
  · intro k hk w
    have I : Integrable (fun v ↦ bloublou L f v k) μ := integrable_bloublou (hf k hk.le) h'f
    have J : Integrable (fun v ↦ ‖v‖ * ‖bloublou L f v k‖) μ := by
      apply ((hf (k+1) (ENat.add_one_le_of_lt hk)).const_mul ((2 * π * ‖L‖) ^ k)).mono'
      · apply continuous_norm.aestronglyMeasurable.mul (aestronglyMeasurable_boublou h'f).norm
      · filter_upwards with v
        simp only [norm_mul, norm_norm]
        calc
        ‖v‖ * ‖bloublou L f v k‖
          ≤ ‖v‖ * ((2 * π * ‖L‖) ^ k * ‖v‖ ^ k * ‖f v‖) := by gcongr; apply norm_bloublou_le
        _ = (2 * π * ‖L‖) ^ k * (‖v‖ ^ (k + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have K : Integrable (fun v ↦ 𝐞 (-((ContinuousLinearMap.toLinearMap₂ L) v) w)
        • bloublou L f v (Nat.succ k)) μ := by
      rw [fourierIntegral_convergent_iff]
      · exact L.continuous₂
      · exact integrable_bloublou (hf (k+1) (ENat.add_one_le_of_lt hk)) h'f
    have E : ContinuousMultilinearMap.curryLeft
        (fourierIntegral 𝐞 μ (ContinuousLinearMap.toLinearMap₂ L)
          (fun v ↦ bloublou L f v (Nat.succ k)) w) =
        fourierIntegral 𝐞 μ (ContinuousLinearMap.toLinearMap₂ L)
          (mul_L L fun v ↦ bloublou L f v k) w := by
      ext w' m
      have B v w' : (bloublou L f v (Nat.succ k)) (Fin.cons w' m) =
          -(2 * ↑π * Complex.I) • (L v) w' • (bloublou L f v k) m := by
        simp [pow_succ, smul_comm (M := ℝ) (N := ℂ) (α := E), Fin.prod_univ_succ, smul_smul]
      have A : (∫ (v : V), 𝐞 (-((ContinuousLinearMap.toLinearMap₂ L) v) w)
            • mul_L L (fun v ↦ bloublou L f v k) v ∂μ) w'
          = ∫ (v : V), (𝐞 (-((ContinuousLinearMap.toLinearMap₂ L) v) w)
            • mul_L L (fun v ↦ bloublou L f v k) v) w' ∂μ := by
        rw [ContinuousLinearMap.integral_apply]
        refine (fourier_integral_convergent_iff continuous_fourierChar ?_ _).1 ?_
        · exact L.continuous₂
          apply ((hf (k+1) (ENat.add_one_le_of_lt hk)).const_mul ((2 * π * ‖L‖) ^ k)).mono'



      simp only [ContinuousMultilinearMap.curryLeft_apply]
      rw [fourierIntegral, ContinuousMultilinearMap.integral_apply K, fourierIntegral, A]
      rw [ContinuousMultilinearMap.integral_apply]
      · simp only [ContinuousMultilinearMap.smul_apply, mul_L,
          ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousMultilinearMap.neg_apply, B]
      · sorry
    rw [E]
    exact hasFDerivAt_fourier L I J w
  · intro k hk
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_bloublou (hf k hk) h'f






#exit


def ContDiff (n : ℕ∞) (f : E → F) : Prop :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p
#align cont_diff ContDiff



section inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [CompleteSpace E]

/-- Notation for the Fourier transform on a real inner product space -/
abbrev integralFourier (f : V → E) (μ : Measure V := by volume_tac) :=
  fourierIntegral 𝐞 μ (innerₛₗ ℝ) f

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
    `fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`. -/
theorem InnerProductSpace.hasFDerivAt_fourier {f : V → E} {μ : Measure V}
    (hf_int : Integrable f μ) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖) μ) (x : V) :
    HasFDerivAt (integralFourier f μ) (integralFourier (mul_L (innerSL ℝ) f) μ x) x := by
  haveI : SecondCountableTopologyEither V (V →L[ℝ] ℝ) :=
    secondCountableTopologyEither_of_left V _ -- for some reason it fails to synthesize this?
  exact VectorFourier.hasFDerivAt_fourier (innerSL ℝ) hf_int hvf_int x

end inner

end VectorFourier

open VectorFourier

lemma hasDerivAt_fourierIntegral [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : ℝ ↦ (-2 * ↑π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h_int : Integrable fun v ↦ mul_L L f v := by
    suffices Integrable fun v ↦ ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [mul_L, neg_smul, neg_mul, Pi.smul_apply] using this.smul (-2 * π * I)
    convert ((ContinuousLinearMap.ring_lmap_equiv_self ℝ
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
      ContinuousLinearMap.map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  rw [fourier_integral_convergent_iff continuous_fourierChar L.continuous₂ w] at h_int
  convert (hasFDerivAt_fourier L hf hf'' w).hasDerivAt using 1
  erw [ContinuousLinearMap.integral_apply h_int]
  simp_rw [ContinuousLinearMap.smul_apply, mul_L, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, L, ContinuousLinearMap.mul_apply', mul_one,
    ← neg_mul, mul_smul]
  rfl
