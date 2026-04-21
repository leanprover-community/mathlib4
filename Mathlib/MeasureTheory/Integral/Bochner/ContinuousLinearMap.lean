/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Operator.CompleteCodomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero

/-!
# Continuous linear maps composed with integration

The goal of this file is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `ContinuousLinearMap.compLp`. We take advantage of this construction here.
-/

public section

open MeasureTheory RCLike
open scoped ENNReal NNReal

variable {X Y E F Fₗ : Type*} [MeasurableSpace X] {μ : Measure X} {𝕜 𝕜' : Type*} [RCLike 𝕜]
  [RCLike 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜 Fₗ] {p : ℝ≥0∞}

namespace ContinuousLinearMap

variable [NormedSpace ℝ F] [NormedSpace ℝ Fₗ]

variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

theorem integral_compLp (L : E →SL[σ] F) (φ : Lp E p μ) :
    ∫ x, (L.compLp φ) x ∂μ = ∫ x, L (φ x) ∂μ :=
  integral_congr_ae <| coeFn_compLp _ _

theorem setIntegral_compLp (L : E →SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, (L.compLp φ) x ∂μ = ∫ x in s, L (φ x) ∂μ :=
  setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)

theorem continuous_integral_comp_L1 (L : E →SL[σ] F) :
    Continuous fun φ : X →₁[μ] E => ∫ x : X, L (φ x) ∂μ := by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

variable [CompleteSpace F] [CompleteSpace Fₗ] [NormedSpace ℝ E]

theorem integral_comp_commSL [CompleteSpace E] (hσ : ∀ (r : ℝ) (x : 𝕜), σ (r • x) = r • σ x)
    (L : E →SL[σ] F) {φ : X → E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ.real s) e,
      map_smulₛₗ, hσ, map_one, smul_assoc, one_smul,
      ← integral_indicator_const (L e) s_meas]
    congr 1 with a
    rw [← Function.comp_def L, Set.indicator_comp_of_zero L.map_zero, Function.comp_apply]
  · intro f g _ f_int g_int hf hg
    simp [L.map_add, integral_add (μ := μ) f_int g_int,
      integral_add (μ := μ) (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg]
  · exact isClosed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
  · intro f g hfg _ hf
    convert hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
    · rw [integral_congr_ae hfg.symm]

theorem integral_comp_comm [CompleteSpace E] (L : E →L[𝕜] Fₗ) {φ : X → E} (φ_int : Integrable φ μ) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := integral_comp_commSL (by simp) L φ_int

theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X → H →L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : (∫ x, φ x ∂μ) v = ∫ x, φ x v ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH | hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuousLinearMap_iff]
      simp [integral, hE, this]

theorem _root_.ContinuousMultilinearMap.integral_apply {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
    {φ : X → ContinuousMultilinearMap 𝕜 M E} (φ_int : Integrable φ μ) (m : ∀ i, M i) :
    (∫ x, φ x ∂μ) m = ∫ x, φ x m ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases! hm : ∀ i, m i ≠ 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ hm]
      simp [integral, hE, this]
    · rcases hm with ⟨i, hi⟩
      simp [ContinuousMultilinearMap.map_coord_zero _ i hi]

variable [CompleteSpace E]

theorem integral_comp_comm' (L : E →L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X → E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]

theorem integral_comp_L1_comm (L : E →L[𝕜] Fₗ) (φ : X →₁[μ] E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.integral_comp_comm (L1.integrable_coeFn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

end LinearIsometry

namespace ContinuousLinearEquiv

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E ≃L[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩ | ⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

end ContinuousLinearEquiv

section ContinuousMap

variable [TopologicalSpace Y] [CompactSpace Y]

lemma ContinuousMap.integral_apply [NormedSpace ℝ E] [CompleteSpace E] {f : X → C(Y, E)}
    (hf : Integrable f μ) (y : Y) : (∫ x, f x ∂μ) y = ∫ x, f x y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
open scoped ContinuousMapZero in
theorem ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y]
    [NormedAlgebra ℝ R] [CompleteSpace R] {f : X → C(Y, R)₀}
    (hf : MeasureTheory.Integrable f μ) (y : Y) :
    (∫ (x : X), f x ∂μ) y = ∫ (x : X), (f x) y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

end ContinuousMap

@[norm_cast]
theorem integral_ofReal {f : X → ℝ} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ) :=
  (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

@[norm_cast]
theorem integral_complex_ofReal {f : X → ℝ} : ∫ x, (f x : ℂ) ∂μ = ∫ x, f x ∂μ := integral_ofReal

theorem integral_re {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ) :=
  (@RCLike.reCLM 𝕜 _).integral_comp_comm hf

theorem integral_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.im (f x) ∂μ = RCLike.im (∫ x, f x ∂μ) :=
  (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

open scoped ComplexConjugate in
theorem integral_conj {f : X → 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ) :=
  (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f

theorem integral_coe_re_add_coe_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, (re (f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I = ∫ x, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul, mul_comm, RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I

theorem integral_re_add_im {f : X → 𝕜} (hf : Integrable f μ) :
    ((∫ x, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x, f x ∂μ := by
  rw [← integral_ofReal, ← integral_ofReal, integral_coe_re_add_coe_im hf]

theorem setIntegral_re_add_im {f : X → 𝕜} {i : Set X} (hf : IntegrableOn f i μ) :
    ((∫ x in i, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x in i, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x in i, f x ∂μ :=
  integral_re_add_im hf

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma swap_integral (f : X → E × F) : (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ :=
  .symm <| (ContinuousLinearEquiv.prodComm ℝ E F).integral_comp_comm f

theorem fst_integral [CompleteSpace F] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm
  · have : ¬(CompleteSpace (E × F)) := fun h ↦ hE <| .fst_of_prod (β := F)
    simp [integral, *]

theorem snd_integral [CompleteSpace E] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← Prod.fst_swap, swap_integral]
  exact fst_integral <| hf.snd.prodMk hf.fst

theorem integral_pair [CompleteSpace E] [CompleteSpace F] {f : X → E} {g : X → F}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prodMk hg
  Prod.ext (fst_integral this) (snd_integral this)

theorem integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (f : X → 𝕜) (c : E) :
    ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c := by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 →L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf, integral_undef, zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

/-
Note that the integrability hypothesis in the two lemmas below is necessary: consider the case
where `A = ℝ × ℝ`, `c = (1,0)`, and `f` is only integrable on the first component.
-/
lemma integral_const_mul_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {f : X → A} (hf : Integrable f μ) {c : A} :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  by_cases hA : CompleteSpace A
  · change ∫ x, ContinuousLinearMap.mul ℝ _ c (f x) ∂μ = ContinuousLinearMap.mul ℝ _ c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

lemma integral_mul_const_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {f : X → A} (hf : Integrable f μ) {c : A} :
    ∫ x, f x * c ∂μ = (∫ x, f x ∂μ) * c := by
  by_cases hA : CompleteSpace A
  · change ∫ x, (ContinuousLinearMap.mul ℝ _).flip c (f x) ∂μ
      = (ContinuousLinearMap.mul ℝ _).flip c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]

theorem integral_withDensity_eq_integral_smul {f : X → ℝ≥0} (f_meas : Measurable f) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ) ?_ ?_ ?_ ?_ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← Set.indicator_smul_apply, integral_indicator s_meas]
    simp only [s_meas, integral_const, Measure.restrict_apply', Set.univ_inter, withDensity_apply,
      measureReal_def]
    rw [lintegral_coe_eq_integral, ENNReal.toReal_ofReal, ← integral_smul_const]
    · rfl
    · exact integral_nonneg fun x => NNReal.coe_nonneg _
    · refine ⟨f_meas.coe_nnreal_real.aemeasurable.aestronglyMeasurable, ?_⟩
      simpa [withDensity_apply _ s_meas, hasFiniteIntegral_iff_enorm] using hs
  · intro u u' _ u_int u'_int h h'
    change
      (∫ x : X, u x + u' x ∂μ.withDensity fun x : X => ↑(f x)) = ∫ x : X, f x • (u x + u' x) ∂μ
    simp_rw [smul_add]
    rw [integral_add u_int u'_int, h, h', integral_add]
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u_int
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u'_int
  · have C1 :
      Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) =>
        ∫ x, u x ∂μ.withDensity fun x => f x :=
      continuous_integral
    have C2 : Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) => ∫ x, f x • u x ∂μ := by
      have : Continuous ((fun u : Lp E 1 μ => ∫ x, u x ∂μ) ∘ withDensitySMulLI (E := E) μ f_meas) :=
        continuous_integral.comp (withDensitySMulLI (E := E) μ f_meas).continuous
      convert this with u
      simp only [Function.comp_apply, withDensitySMulLI_apply]
      exact integral_congr_ae (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp.symm
    exact isClosed_eq C1 C2
  · intro u v huv _ hu
    rw [← integral_congr_ae huv, hu]
    apply integral_congr_ae
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx
    rcases eq_or_ne (f x) 0 with (h'x | h'x)
    · simp only [h'x, zero_smul]
    · rw [hx _]
      simpa only [Ne, ENNReal.coe_eq_zero] using h'x

theorem integral_withDensity_eq_integral_smul₀ {f : X → ℝ≥0} (hf : AEMeasurable f μ) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.measurable_mk _
    _ = ∫ x, f x • g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]

theorem integral_withDensity_eq_integral_toReal_smul₀ {f : X → ℝ≥0∞} (f_meas : AEMeasurable f μ)
    (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ := by
  dsimp only [ENNReal.toReal, ← NNReal.smul_def]
  rw [← integral_withDensity_eq_integral_smul₀ f_meas.ennreal_toNNReal,
    withDensity_congr_ae (coe_toNNReal_ae_eq hf_lt_top)]

theorem integral_withDensity_eq_integral_toReal_smul {f : X → ℝ≥0∞} (f_meas : Measurable f)
    (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ :=
  integral_withDensity_eq_integral_toReal_smul₀ f_meas.aemeasurable hf_lt_top g

theorem setIntegral_withDensity_eq_setIntegral_smul₀ {f : X → ℝ≥0} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul₀ hf]

theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀ {f : X → ℝ≥0∞} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E)
    (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

theorem setIntegral_withDensity_eq_setIntegral_smul {f : X → ℝ≥0} (f_meas : Measurable f)
    (g : X → E) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_smul₀ f_meas.aemeasurable _ hs

theorem setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X → ℝ≥0∞} {s : Set X}
    (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.aemeasurable hf_top g hs

theorem setIntegral_withDensity_eq_setIntegral_smul₀' [SFinite μ] {f : X → ℝ≥0} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity' s, integral_withDensity_eq_integral_smul₀ hf]

theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀' [SFinite μ] {f : X → ℝ≥0∞} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity' s, integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]

theorem setIntegral_withDensity_eq_setIntegral_toReal_smul' [SFinite μ] {f : X → ℝ≥0∞} (s : Set X)
    (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hf.aemeasurable hf_top g
