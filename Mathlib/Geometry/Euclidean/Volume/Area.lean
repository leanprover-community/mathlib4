/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.ENat
import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Area formula
-/

open MeasureTheory RealInnerProductSpace Module LinearMap
section random

variable {𝕜 U V W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W]

theorem eixsts_polar_decomposition (f : U →ₗ[𝕜] V) (h : f.ker = ⊥) :
    ∃ (u : U →ₗᵢ[𝕜] V) (p : U →ₗ[𝕜] U),
    u.toLinearMap ∘ₗ p = f ∧ p.ker = ⊥ := by
  have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
    obtain hrank := f.finrank_range_add_finrank_ker
    rw [h] at hrank
    simpa [h] using hrank
  let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
  let bv : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range :=
    (stdOrthonormalBasis 𝕜 f.range).reindex (by rw [hrank])
  let g := OrthonormalBasis.equiv bu bv (Equiv.refl _)
  use (Submodule.subtypeₗᵢ f.range).comp g.toLinearIsometry, g.symm.toLinearMap.comp f.rangeRestrict
  constructor
  · change f.range.subtype ∘ₗ (g.toLinearMap ∘ₗ g.symm.toLinearMap) ∘ₗ f.rangeRestrict = f
    simp
  · simpa using h

end random


variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ U] in
theorem image_ball {r : ℝ} (hr : 0 < r) : (r • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 =
    Metric.ball 0 r := by
  ext x
  simp only [smul_apply, id_coe, id_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · intro ⟨y, h1, h2⟩
    rw [← h2, norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg hr.le]
    apply mul_lt_of_lt_one_right hr h1
  · intro h
    use r⁻¹ • x
    constructor
    · rw [norm_smul]
      rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg hr.le]
      exact (inv_mul_lt_one₀ hr).mpr h
    · simp [smul_smul, hr.ne.symm]

theorem volume_ball_ne_zero [MeasurableSpace U] [BorelSpace U] [Nontrivial U] :
    volume (Metric.ball 0 1 : Set U) ≠ 0 := by
  rw [InnerProductSpace.volume_ball]
  positivity

theorem volume_ball_ne_top [MeasurableSpace U] [BorelSpace U] :
    volume (Metric.ball 0 1 : Set U) ≠ ⊤ := by
  nontriviality U
  rw [InnerProductSpace.volume_ball]
  simp

structure Eprop (B : Set U) (t ε : ℝ) (f : U → V) (f' : U → U →L[ℝ] V)
    (c : U) (T : U →ₗ[ℝ] U) (i : PNat) (b : U) where
  mem_B : b ∈ B
  mem_ball : b ∈ Metric.ball c (1 / i : ℝ)
  h1left : ∀ u : U, (t⁻¹ + ε) * ‖T u‖ ≤ ‖f' b u‖
  h1right : ∀ u : U, ‖f' b u‖ ≤ (t - ε) * ‖T u‖
  h2 : ∀ a ∈ Metric.ball c (2 / i : ℝ) ∩ B, ‖f a - f b - f' b (a - b)‖ ≤ ε * ‖T (a - b)‖

-- by aristotle
theorem measurable_Eprop.extracted_1_4 {U : Type*} {V : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace U] [BorelSpace U]
    [CompleteSpace V]
    (t ε : ℝ) (f' : U → U →L[ℝ] V) (hfm : Measurable f') (T : U →ₗ[ℝ] U) :
    Measurable fun a ↦ ∀ (u : U), (t⁻¹ + ε) * ‖T u‖ ≤ ‖f' a u‖ := by
  have h_closed : IsClosed {L : U →L[ℝ] V | ∀ u : U, (t⁻¹ + ε) * ‖T u‖ ≤ ‖L u‖} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun u => isClosed_le continuous_const (by fun_prop)
  apply MeasurableSet.mem (h_closed.measurableSet.preimage hfm)


-- by aristotle
theorem measurable_Eprop.extracted_1_6 {U : Type*} {V : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace U] [BorelSpace U]
    [CompleteSpace V]
    (t ε : ℝ) (f' : U → U →L[ℝ] V) (hfm : Measurable f') (T : U →ₗ[ℝ] U) :
    Measurable fun a ↦ ∀ (u : U), ‖f' a u‖ ≤ (t - ε) * ‖T u‖ := by
  have h_closed : IsClosed {L : U →L[ℝ] V | ∀ u : U, ‖L u‖ ≤ (t - ε) * ‖T u‖} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun u => isClosed_le (by fun_prop) continuous_const
  exact MeasurableSet.mem (h_closed.measurableSet.preimage hfm)

-- by aristotle
theorem measurable_Eprop.extracted_1_5 {U : Type*} {V : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace U] [BorelSpace U]
    [CompleteSpace V] (B : Set U) (hm : MeasurableSet B)
    (ε : ℝ) (f : U → V) (hcont : ContinuousOn f B) (f' : U → U →L[ℝ] V) (hfm : Measurable f')
    (T : U →ₗ[ℝ] U) (c : U) (i : PNat) :
    Measurable fun b ↦ (∀ a ∈ Metric.ball c (2 / ↑↑i) ∩ B, ‖f a - f b - f' b (a - b)‖ ≤
    ε * ‖T (a - b)‖) ∧ b ∈ B := by
  rw [← measurableSet_setOf]
  set r := (2 : ℝ) / ↑↑i
  -- Define C ⊆ (U →L[ℝ] V) × B as the "closed constraint set"
  set C : Set ((U →L[ℝ] V) × B) :=
    {p | ∀ a ∈ Metric.ball c r ∩ B,
      ‖f a - f p.2.val - p.1 (a - p.2.val)‖ ≤ ε * ‖T (a - p.2.val)‖}
  -- Auxiliary: the restriction of f to B is continuous
  have hf_cont : Continuous (fun (b : B) => f b.val) :=
    continuousOn_iff_continuous_restrict.mp hcont
  -- Auxiliary: evaluation of ContinuousLinearMap is continuous
  have heval : Continuous (fun (p : (U →L[ℝ] V) × U) => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  -- Step 1: C is closed (arbitrary intersection of closed sets)
  have hC_closed : IsClosed C := by
    have hC_eq : C = ⋂ (a : U) (_ : a ∈ Metric.ball c r ∩ B),
        {p : (U →L[ℝ] V) × B |
          ‖f a - f p.2.val - p.1 (a - p.2.val)‖ ≤ ε * ‖T (a - p.2.val)‖} := by
      ext p; simp [C, Set.mem_iInter]
    rw [hC_eq]
    apply isClosed_biInter
    intro a _
    apply isClosed_le
    · -- ‖f a - f p.2.val - p.1 (a - p.2.val)‖ is continuous in p
      refine Continuous.norm ?_
      exact (continuous_const.sub (hf_cont.comp continuous_snd)).sub
        (heval.comp (Continuous.prodMk continuous_fst
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd))))
    · -- ε * ‖T (a - p.2.val)‖ is continuous in p
      exact continuous_const.mul
        (T.toContinuousLinearMap.continuous.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd))).norm
  -- Step 2: C is measurable (since (U →L[ℝ] V) × B has OpensMeasurableSpace)
  have hC_meas : MeasurableSet C := hC_closed.measurableSet
  -- Step 3: ψ : B → (U →L[ℝ] V) × B is measurable
  set ψ : B → (U →L[ℝ] V) × B := fun b => (f' b.val, b) with hψ_def
  have hψ_meas : Measurable ψ :=
    Measurable.prod (hfm.comp measurable_subtype_coe) measurable_id
  -- Step 4: ψ⁻¹'(C) is measurable in B
  have hpre : MeasurableSet (ψ ⁻¹' C) := hψ_meas hC_meas
  -- Step 5: The image under Subtype.val is measurable in U
  have himg : MeasurableSet (Subtype.val '' (ψ ⁻¹' C)) := hm.subtype_image hpre
  -- Step 6: Our set equals this image
  convert himg using 1
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨hball, hB⟩
    exact ⟨⟨b, hB⟩, hball, rfl⟩
  · rintro ⟨⟨b', hB'⟩, hball, rfl⟩
    exact ⟨hball, hB'⟩

theorem measurable_Eprop [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (B : Set U) (hm : MeasurableSet B) (t ε : ℝ) (f : U → V) (f' : U → U →L[ℝ] V)
    (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x) (hfm : Measurable f')
    (c : U) (T : U →ₗ[ℝ] U) (i : PNat) :
    Measurable (Eprop B t ε f f' c T i) := by
  have hdiff (b : U) (hb : b ∈ B) : DifferentiableWithinAt ℝ f B b :=
    (hf' b hb).differentiableWithinAt
  have hcont : ContinuousOn f B := by
    intro b hb
    apply (hdiff b hb).continuousWithinAt
  suffices Measurable (fun b ↦ (b ∈ Metric.ball c (1 / i : ℝ))
      ∧ (∀ u : U, (t⁻¹ + ε) * ‖T u‖ ≤ ‖f' b u‖) ∧
      (∀ u : U, ‖f' b u‖ ≤ (t - ε) * ‖T u‖) ∧
      (∀ a ∈ Metric.ball c (2 / i : ℝ) ∩ B, ‖f a - f b - f' b (a - b)‖ ≤ ε * ‖T (a - b)‖) ∧
      b ∈ B) by
    convert this
    grind [Eprop]
  apply Measurable.and
  · measurability
  apply Measurable.and
  · apply measurable_Eprop.extracted_1_4
    exact hfm
  apply Measurable.and
  · apply measurable_Eprop.extracted_1_6
    exact hfm
  apply measurable_Eprop.extracted_1_5 B hm _ _ hcont
  exact hfm

namespace Eprop

variable {B : Set U} {t ε : ℝ} {f : U → V} {f' : U → U →L[ℝ] V}
  {c : U} {T : U →ₗ[ℝ] U} {i : PNat} {b : U}

omit [FiniteDimensional ℝ U] in
theorem mem_ball2 (hb : Eprop B t ε f f' c T i b) : b ∈ Metric.ball c (2 / i : ℝ) := by
  have hbc := hb.mem_ball
  rw [Metric.mem_ball] at ⊢ hbc
  apply hbc.trans_le
  apply (div_le_div_iff₀ (by simp) (by simp)).mpr
  grind

omit [FiniteDimensional ℝ U] in
theorem h3left (hb : Eprop B t ε f f' c T i b) {a : U} (ha : a ∈ Metric.ball c (2 / i : ℝ) ∩ B) :
    t⁻¹ * ‖T (a - b)‖ ≤ ‖f a - f b‖ := by
  obtain h := hb.h1left (a - b)
  rw [add_mul, ← le_sub_iff_add_le] at h
  apply h.trans
  rw [sub_le_comm]
  apply le_trans ?_ (hb.h2 a ha)
  apply (norm_sub_norm_le _ _).trans
  rw [norm_sub_rev]

omit [FiniteDimensional ℝ U] in
theorem h3right (hb : Eprop B t ε f f' c T i b) {a : U} (ha : a ∈ Metric.ball c (2 / i : ℝ) ∩ B) :
    ‖f a - f b‖ ≤ t * ‖T (a - b)‖ := by
  obtain h := hb.h1right (a - b)
  rw [sub_mul, le_sub_iff_add_le] at h
  apply le_trans ?_ h
  rw [← sub_le_iff_le_add']
  apply le_trans ?_ (hb.h2 a ha)
  apply norm_sub_norm_le

theorem hclaimright [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (hb : Eprop B t ε f f' c T i b) (hεright : 1 < t - ε) :
    (f' b).normDet ≤ (t - ε) ^ finrank ℝ U * |T.det| := by
  nontriviality U
  by_cases hT : T.ker = ⊥
  · by_cases hf : (f' b).ker = ⊥
    · let T' := LinearEquiv.ofInjectiveEndo T (LinearMap.ker_eq_bot.mp hT)
      have h (v : U) := hb.h1right (T'.symm v)
      have hsymm (v : U) : T (T'.symm v) = v := by
        change T' (T'.symm v) = v
        simp
      simp_rw [hsymm] at h
      obtain ⟨u, p, hu, _⟩ := eixsts_polar_decomposition (f' b) (by simpa using hf)
      have hball : (p ∘ₗ T'.symm.toLinearMap) '' Metric.ball 0 1
          ⊆ ((t - ε) • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 := by
        rw [image_ball (lt_trans (by norm_num) hεright)]
        intro v
        simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Set.mem_image, Metric.mem_ball, dist_zero_right, forall_exists_index, and_imp]
        intro x hx rfl
        suffices ‖f' b (T'.symm x)‖ < ↑t - ε by
          change ‖(f' b).toLinearMap (T'.symm x)‖ < ↑t - ε at this
          rw [← hu] at this
          simpa using this
        apply lt_of_le_of_lt (h x)
        exact mul_lt_of_lt_one_right (lt_trans (by norm_num) hεright) hx
      obtain hmeasure := MeasureTheory.measure_mono hball (μ := volume)
      simp_rw [MeasureTheory.Measure.addHaar_image_linearMap] at hmeasure
      rw [ENNReal.mul_le_mul_iff_left volume_ball_ne_zero volume_ball_ne_top] at hmeasure
      rw [ENNReal.ofReal_le_ofReal_iff (by simp)] at hmeasure
      simp only [det_comp, LinearEquiv.det_coe_symm, abs_mul, abs_inv] at hmeasure
      rw [mul_inv_le_iff₀ (by simp [← LinearEquiv.coe_det])] at hmeasure
      convert hmeasure
      · rw [← hu]
        rw [normDet_comp_of_finrank_eq _ _ (by simp)]
        simp [u.normDet_eq_one, normDet_eq_norm_det]
      · suffices (0 : ℝ) ≤ t - ε by simp [abs_of_nonneg this]
        apply (lt_trans (by norm_num) hεright).le
    · rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hf]
      positivity
  · suffices (f' b).normDet = 0 by
      simp [this, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hT]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    rw [LinearMap.mem_ker] at hv
    obtain h := hb.h1right v
    rw [normDet_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    refine ⟨v, ?_, hv0⟩
    simpa [hv] using h

theorem hclaimleft [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (hb : Eprop B t ε f f' c T i b) (hεpos : 0 < t⁻¹ + ε) :
    (t⁻¹ + ε) ^ finrank ℝ U * |T.det| ≤ (f' b).normDet := by
  nontriviality U
  by_cases hT : T.ker = ⊥
  · by_cases hf : (f' b).ker = ⊥
    · let T' := LinearEquiv.ofInjectiveEndo T (LinearMap.ker_eq_bot.mp hT)
      obtain ⟨u, p, hu, hp⟩ := eixsts_polar_decomposition (f' b) (by simpa using hf)
      have hball : ((t⁻¹ + ε) • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 ⊆
          (p ∘ₗ T'.symm.toLinearMap) '' Metric.ball 0 1 := by
        rw [image_ball (hεpos)]
        intro v
        simp only [Metric.mem_ball, dist_zero_right, coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply, Set.mem_image]
        intro hv
        obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hp) v
        use T' w
        simp only [LinearEquiv.symm_apply_apply, hw, and_true]
        obtain h : ∀ (u : U), (t⁻¹ + ε) * ‖T u‖ ≤ ‖(f' b).toLinearMap u‖ := hb.h1left
        specialize h w
        simp_rw [← hu] at h
        simp only [coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply, hw,
          LinearIsometry.norm_map] at h
        obtain h := h.trans_lt hv
        rw [mul_lt_iff_lt_one_right hεpos] at h
        exact h
      obtain hmeasure := MeasureTheory.measure_mono hball (μ := volume)
      simp_rw [MeasureTheory.Measure.addHaar_image_linearMap] at hmeasure
      rw [ENNReal.mul_le_mul_iff_left volume_ball_ne_zero volume_ball_ne_top] at hmeasure
      rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hmeasure
      simp only [det_smul, det_id, mul_one, abs_pow, det_comp,
        LinearEquiv.det_coe_symm, abs_mul, abs_inv] at hmeasure
      rw [le_mul_inv_iff₀ (by simp [← LinearEquiv.coe_det])] at hmeasure
      convert hmeasure using 3
      · rw [abs_of_nonneg hεpos.le]
      · rw [← hu]
        rw [normDet_comp_of_finrank_eq _ _ (by simp)]
        simp [u.normDet_eq_one, normDet_eq_norm_det]
    · suffices LinearMap.det T = 0 by
        simp [this, LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hf]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
      rw [LinearMap.mem_ker] at hv
      obtain h := hb.h1left v
      rw [det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
      refine ⟨v, ?_, hv0⟩
      rw [ContinuousLinearMap.coe_coe] at hv
      rw [hv, norm_zero] at h
      obtain h := le_antisymm h (mul_nonneg hεpos.le (by simp))
      simpa [hεpos.ne.symm] using h
  · simpa [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hT] using normDet_nonneg _

end Eprop

structure Piece [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] (t : NNReal) (f : U → V)
    (f' : U → U →L[ℝ] V)
    (measureProp : Prop) where
  E : Set U
  measurablSet : measureProp → MeasurableSet E
  T : U ≃ₗ[ℝ] U
  lipschitz : LipschitzOnWith t (f ∘ T.symm) (T '' E)
  lipschitz_inv : LipschitzOnWith t (T ∘ f.invFunOn E) (f '' E)
  det_le : ∀ x ∈ E, (↑t)⁻¹ ^ finrank ℝ U * |T.toLinearMap.det| ≤ (f' x).normDet
  le_det : ∀ x ∈ E, (f' x).normDet ≤ t ^ finrank ℝ U * |T.toLinearMap.det|

def Piece.mk' [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (B : Set U) (t : NNReal) (ht : 1 < t) (ε : ℝ)
    (hεpos : 0 < (↑t)⁻¹ + ε) (h0ε : 0 ≤ ε) (hεright : 1 < t - ε)
    (f : U → V) (f' : U → U →L[ℝ] V) (hf : Set.InjOn f B)
    (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (c : U) (T : U ≃ₗ[ℝ] U) (i : PNat) :
    Piece t f f' (MeasurableSet B ∧ Measurable f') where
  E := {b | Eprop B t ε f f' c T i b}
  measurablSet := by
    rintro ⟨hB, hfm⟩
    rw [measurableSet_setOf]
    apply measurable_Eprop B hB _ _ _ _ hf' hfm
  T := T
  lipschitz := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simp only [Set.mem_image, Set.mem_setOf_eq] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply, dist_eq_norm, ← map_sub]
    apply hb.h3right ⟨ha.mem_ball2, ha.mem_B⟩
  lipschitz_inv := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simp only [Set.mem_image, Set.mem_setOf_eq] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    simp only [Function.comp_apply, dist_eq_norm, ← map_sub]
    have hinj : Set.InjOn f {b | Eprop B (↑t) ε f f' c (↑T) i b} := by
      apply hf.mono
      intro b hb
      rw [Set.mem_setOf_eq] at hb
      exact hb.mem_B
    rw [Set.InjOn.leftInvOn_invFunOn hinj (by simpa using ha)]
    rw [Set.InjOn.leftInvOn_invFunOn hinj (by simpa using hb)]
    rw [← inv_mul_le_iff₀ (by
      rw [NNReal.coe_pos]
      apply lt_trans (by norm_num) ht
    )]
    apply hb.h3left ⟨ha.mem_ball2, ha.mem_B⟩
  det_le x hx := by
    refine le_trans ?_ (Eprop.hclaimleft hx hεpos)
    refine mul_le_mul_of_nonneg_right ?_ (by simp)
    apply pow_le_pow_left₀ (by simp)
    simpa using h0ε
  le_det x hx := by
    apply (Eprop.hclaimright hx hεright).trans
    refine mul_le_mul_of_nonneg_right ?_ (by simp)
    have h := (show (0 : ℝ) < 1 by norm_num).trans hεright
    apply pow_le_pow_left₀ (by simpa using h.le)
    simpa using h0ε

-- begin Aristotle
lemma ContinuousLinearMap.exists_pos_lower_bound
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    {f : U →L[ℝ] U} (hf : f.ker = ⊥) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : U, c * ‖x‖ ≤ ‖f x‖ := by
  -- Use the fact that a linear map on a finite-dimensional space is injective if and only if it
  -- is bounded below.
  have h_inj : Function.Injective f := by
    exact LinearMap.ker_eq_bot.mp hf;
  obtain ⟨ K, hK ⟩ := f.toLinearMap.injective_iff_antilipschitz.mp h_inj;
  refine ⟨ 1 / K, ?_, ?_ ⟩;
  · exact one_div_pos.mpr ( NNReal.coe_pos.mpr hK.1 );
  · intro x; have := hK.2.le_mul_dist x 0
    simp only [dist_zero_right, coe_coe, map_zero] at this
    simp only [gt_iff_lt, coe_coe] at hK
    simp only [div_eq_inv_mul, mul_one, ge_iff_le]
    rwa [ inv_mul_le_iff₀ ( NNReal.coe_pos.mpr hK.1 ) ]

theorem approx_linear_map {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    {s : Set (U →L[ℝ] U)} (hs : Dense s) {f : U →L[ℝ] U} (hf : f.ker = ⊥)
    {a b : ℝ} (ha : a < 1) (hb : 1 < b) :
    ∃ g ∈ s, (∀ x, a * ‖g x‖ ≤ ‖f x‖) ∧ (∀ x, ‖f x‖ ≤ b * ‖g x‖) := by
  -- Use `ContinuousLinearMap.exists_pos_lower_bound` to get c > 0 with c * ‖x‖ ≤ ‖f x‖ for all
  -- x.
  obtain ⟨c, hc⟩ : ∃ c > 0, ∀ x : U, c * ‖x‖ ≤ ‖f x‖ := by
    exact ContinuousLinearMap.exists_pos_lower_bound hf;
  -- Choose δ such that δ < c and δ < c*(1-a) and δ < c*(1-1/b).
  obtain ⟨δ, hδ_pos, hδ_lt_c, hδ_lt_ca, hδ_lt_cb⟩ : ∃ δ > 0, δ < c ∧ δ < c * (1 - a) ∧
      δ < c * (1 - 1 / b) := by
    obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ > 0, δ < min (c * (1 - a)) (c * (1 - 1 / b)) := by
      exact exists_between ( lt_min ( mul_pos hc.1 ( sub_pos.2 ha ) ) ( mul_pos hc.1 ( sub_pos.2
        ( by rw [ div_lt_iff₀ ] <;> linarith ) ) ) );
    exact ⟨ Min.min δ c / 2, half_pos ( lt_min hδ_pos hc.1 ), by
      linarith [ min_le_left δ c, min_le_right δ c ],
      by linarith [ min_le_left δ c, min_le_right δ c,
        min_le_left ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ),
        min_le_right ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ) ],
      by linarith [ min_le_left δ c, min_le_right δ c,
        min_le_left ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ),
        min_le_right ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ) ] ⟩;
  -- Choose g ∈ s such that ‖g - f‖ < δ.
  obtain ⟨g, hg_s, hg_dist⟩ : ∃ g ∈ s, ‖g - f‖ < δ := by
    simpa [ dist_eq_norm' ] using hs.exists_dist_lt f hδ_pos;
  refine ⟨ g, hg_s, fun x => ?_, fun x => ?_ ⟩;
  · have := ContinuousLinearMap.le_opNorm ( g - f ) x;
    simp_all
    nlinarith [ norm_nonneg x, norm_nonneg ( g x - f x ), norm_nonneg ( g x ),
      norm_nonneg ( f x ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hb ) ),
      hc.2 x, mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg x ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( g x - f x ) ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( g x ) ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( f x ) ),
      norm_sub_norm_le ( g x ) ( f x ) ];
  · -- Using the triangle inequality and the bounds on δ, we get:
    have h_triangle : ‖g x‖ ≥ ‖f x‖ - δ * ‖x‖ := by
      have := ContinuousLinearMap.le_of_opNorm_le _ hg_dist.le x;
      simpa using norm_sub_le ( g x ) ( ( g - f ) x ) |> le_trans <| by simpa using this;
    nlinarith [ hc.2 x, norm_nonneg x, norm_nonneg ( f x ), norm_nonneg ( g x ),
      mul_div_cancel₀ 1 ( by linarith : b ≠ 0 ),
      mul_le_mul_of_nonneg_left hδ_lt_cb.le ( norm_nonneg x ),
        mul_le_mul_of_nonneg_left hδ_lt_ca.le ( norm_nonneg x ),
        mul_le_mul_of_nonneg_left hδ_lt_c.le ( norm_nonneg x ) ]

-- end Aristotle

theorem lemma3_3 [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    ∃ (Es : Set (Piece t f f' (MeasurableSet B ∧ Measurable f'))),
      Es.Countable ∧ B = ⋃ p ∈ Es, p.E := by
  have ht' : (1 : ℝ) < t := by simpa using ht
  let ε : ℝ := (t - 1) / (2 * t)
  have h0ε' : 0 < ε := by
    unfold ε
    apply div_pos (by simpa using ht')
    positivity
  have h0ε : 0 ≤ ε := by
    unfold ε
    apply div_nonneg (by simpa using ht'.le)
    simp
  have hεleft : (↑t)⁻¹ + ε < 1 := by
    unfold ε
    refine lt_of_mul_lt_mul_left ?_ (show 0 ≤ (2 * t : ℝ) by positivity)
    rw [mul_add, mul_assoc, mul_inv_cancel₀ (by positivity)]
    rw [mul_div_cancel₀ _ (by positivity)]
    linarith
  have hεpos : 0 < (↑t)⁻¹ + ε := by
    unfold ε
    apply add_pos (by positivity)
    apply div_pos (by linarith) (by positivity)
  have hεright : 1 < t - ε := by
    unfold ε
    refine lt_of_mul_lt_mul_left ?_ (show 0 ≤ (2 * t : ℝ) by positivity)
    rw [mul_sub, mul_div_cancel₀ _ (by positivity)]
    apply lt_of_sub_pos
    suffices (0 : ℝ) < (t - 1) * (2 * t - 1) by
      convert this using 1
      ring
    apply mul_pos (by linarith) (by linarith)
  have hU := TopologicalSpace.exists_countable_dense B
  have hUU := TopologicalSpace.exists_countable_dense (U →L[ℝ] U)
  let C := hU.choose
  let S : Set (U ≃ₗ[ℝ] U) := LinearEquiv.toLinearMap ⁻¹'
    (ContinuousLinearMap.toLinearMap '' hUU.choose)
  use ⋃ c ∈ C, ⋃ T ∈ S, Set.range (Piece.mk' B t ht ε hεpos h0ε hεright f f' hf hf' c T)
  constructor
  · rw [Set.Countable.biUnion_iff (by
      apply hU.choose_spec.1)]
    intro _ _
    rw [Set.Countable.biUnion_iff (by
      refine Set.Countable.preimage ?_ (LinearEquiv.toLinearMap_injective)
      apply hUU.choose_spec.1.image)]
    intro _ _
    apply Set.countable_range
  apply subset_antisymm
  · intro b hb
    obtain ⟨o, s, hos, hs⟩ := eixsts_polar_decomposition (f' b).toLinearMap (hker b hb)
    simp only [Set.mem_iUnion, Set.mem_range, exists_prop, Set.iUnion_exists, Set.biUnion_and',
      Set.iUnion_iUnion_eq', Piece.mk', Set.mem_setOf_eq]
    have hs' : s.toContinuousLinearMap.ker = ⊥ := hs
    obtain ⟨T', hT', hTleft, hTright⟩ := approx_linear_map hUU.choose_spec.2 hs' hεleft hεright
    have hTker : T'.ker = ⊥ := by
      contrapose! hTright with hker
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
      use x
      rw [mem_ker, ContinuousLinearMap.coe_coe] at hx
      suffices x ∉ s.ker by
        simpa [hx]
      simpa [hs] using hx0
    let T : U ≃ₗ[ℝ] U := LinearEquiv.ofInjectiveEndo T'.toLinearMap (LinearMap.ker_eq_bot.mp hTker)
    have hTS : T ∈ S := by
      simp only [Set.mem_preimage, Set.mem_image, S]
      use T', hT'
      rfl
    have hT : T.symm.toLinearMap ≠ 0 := by
      intro h
      simpa using congr(LinearMap.ker $h)
    have hbound : 0 < ε / ‖T.symm.toContinuousLinearMap‖ := by
      apply div_pos h0ε'
      simpa using hT
    obtain ⟨r, hr0, hr⟩ := Metric.mem_nhdsWithin_iff.mp <|
      (hf' b hb).isLittleO.bound hbound
    let i := Nat.toPNat ⌈3 / r⌉₊ (by simpa using hr0)
    have hi : (0 : ℝ) < 1 / i := by simp
    obtain ⟨c, hcm, hc⟩ := Dense.exists_dist_lt hU.choose_spec.2 ⟨b, hb⟩ hi
    have hc : dist b c < 1 / i := hc
    use c, hcm, T, hTS, i
    exact {
      mem_B := hb
      mem_ball := by
        simpa using hc
      h1left u := by
        change ((↑t)⁻¹ + ε) * ‖T' u‖ ≤ ‖(f' b).toLinearMap u‖
        rw [← hos]
        simpa using hTleft u
      h1right u := by
        change ‖(f' b).toLinearMap u‖ ≤ (↑t - ε) * ‖T' u‖
        rw [← hos]
        simpa using hTright u
      h2 a ha := by
        obtain ⟨ha, haB⟩ := ha
        have hab : a ∈ Metric.ball b r := by
          rw [Metric.mem_ball] at ⊢ ha
          rw [dist_comm] at hc
          apply (dist_triangle _ c.val _).trans_lt
          apply lt_of_lt_of_le (add_lt_add ha hc)
          rw [← add_div]
          norm_num
          change 3 / ⌈3 / r⌉₊ ≤ r
          rw [div_le_comm₀ (by simpa using hr0) hr0]
          exact Nat.le_ceil (3 / r)
        apply (hr ⟨hab, haB⟩).trans
        rw [div_mul_eq_mul_div, div_le_iff₀ (by simpa using hT), mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ h0ε
        rw [mul_comm]
        convert ContinuousLinearMap.le_opNorm T.symm.toContinuousLinearMap (T.toLinearMap (a - b))
          using 1
        simp
    }
  simp [Piece.mk']
  grind [Eprop.mem_B]


theorem nonempty_piece [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) : (lemma3_3 ht hf hf' hker).choose.Nonempty := by
  contrapose! hB with h
  obtain hunion := (lemma3_3 ht hf hf' hker).choose_spec.2
  simpa [h] using hunion

noncomputable def pieceSeq' [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) : ℕ → Piece t f f' (MeasurableSet B ∧ Measurable f') :=
  (Set.Countable.exists_eq_range (lemma3_3 ht hf hf' hker).choose_spec.1
    (nonempty_piece ht hf hf' hB hker)).choose


theorem iUnion_pieceSeq' [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    B = ⋃ k, (pieceSeq' ht hf hf' hB hker k).E := by
  obtain hmem := (Set.Countable.exists_eq_range (lemma3_3 ht hf hf' hker).choose_spec.1
    (nonempty_piece ht hf hf' hB hker)).choose_spec
  rw [pieceSeq']
  conv_lhs => rw [(lemma3_3 ht hf hf' hker).choose_spec.2]
  ext i
  constructor
  · simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
    grind
  · intro h
    simp only [Set.mem_iUnion] at h ⊢
    grind

noncomputable def pieceSeq [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) (k : ℕ) : Piece t f f' (MeasurableSet B ∧ Measurable f') where
  E := (pieceSeq' ht hf hf' hB hker k).E \ ⋃ j < k, (pieceSeq' ht hf hf' hB hker j).E
  measurablSet hBm := by
    apply ((pieceSeq' ht hf hf' hB hker k).measurablSet hBm).diff
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro _
    exact (pieceSeq' ht hf hf' hB hker i).measurablSet hBm
  T := (pieceSeq' ht hf hf' hB hker k).T
  lipschitz := (pieceSeq' ht hf hf' hB hker k).lipschitz.mono (Set.image_mono Set.diff_subset)
  lipschitz_inv := by
    have hinj' : Set.InjOn f (pieceSeq' ht hf hf' hB hker k).E := by
      apply hf.mono
      conv =>
        right
        rw [iUnion_pieceSeq' ht hf hf' hB hker]
      apply Set.subset_iUnion _ k
    have hinj : Set.InjOn f
        ((pieceSeq' ht hf hf' hB hker k).E \ ⋃ j, ⋃ (_ : j < k),
        (pieceSeq' ht hf hf' hB hker j).E) := by
      apply hf.mono
      apply Set.diff_subset.trans
      conv =>
        right
        rw [iUnion_pieceSeq' ht hf hf' hB hker]
      apply Set.subset_iUnion _ k
    obtain h := (pieceSeq' ht hf hf' hB hker k).lipschitz_inv
    unfold LipschitzOnWith at ⊢ h
    intro x hx y hy
    convert h (Set.mem_of_mem_of_subset hx (Set.image_mono Set.diff_subset))
      (Set.mem_of_mem_of_subset hy (Set.image_mono Set.diff_subset)) using 2
    <;> simp only [Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
    · obtain ⟨x', hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
      apply hinj
      · apply Function.invFunOn_apply_mem hx'
      · rw [Set.InjOn.leftInvOn_invFunOn hinj'
          (Set.mem_of_mem_of_subset hx' Set.diff_subset)]
        exact hx'
      · rw [Set.InjOn.leftInvOn_invFunOn hinj hx']
        rw [Set.InjOn.leftInvOn_invFunOn hinj'
          (Set.mem_of_mem_of_subset hx' Set.diff_subset)]
    · obtain ⟨x', hx', rfl⟩ := (Set.mem_image _ _ _).mp hy
      apply hinj
      · apply Function.invFunOn_apply_mem hx'
      · rw [Set.InjOn.leftInvOn_invFunOn hinj'
          (Set.mem_of_mem_of_subset hx' Set.diff_subset)]
        exact hx'
      · rw [Set.InjOn.leftInvOn_invFunOn hinj hx']
        rw [Set.InjOn.leftInvOn_invFunOn hinj'
          (Set.mem_of_mem_of_subset hx' Set.diff_subset)]
  det_le x hx :=
    (pieceSeq' ht hf hf' hB hker k).det_le x (Set.mem_of_mem_of_subset hx Set.diff_subset)
  le_det x hx :=
    (pieceSeq' ht hf hf' hB hker k).le_det x (Set.mem_of_mem_of_subset hx Set.diff_subset)


theorem iUnion_pieceSeq [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    B = ⋃ k, (pieceSeq ht hf hf' hB hker k).E := by
  conv_lhs => rw [iUnion_pieceSeq' ht hf hf' hB hker]
  apply subset_antisymm
  · intro x
    simp only [Set.mem_iUnion]
    intro h
    classical
    use Nat.find h
    simp only [pieceSeq, Nat.lt_find_iff, Set.mem_diff, Set.mem_iUnion, exists_prop, not_exists,
      not_and]
    constructor
    · exact Nat.find_spec h
    · intro y hy
      apply Nat.find_min h
      rw [Nat.lt_find_iff]
      exact hy
  · rw [Set.iUnion_subset_iff]
    intro k
    simp only [pieceSeq]
    apply subset_trans Set.diff_subset
    apply Set.subset_iUnion _ k

theorem pieceSeq_subset [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) (j : ℕ) :
    (pieceSeq ht hf hf' hB hker j).E ⊆ B := by
  conv_rhs => rw [iUnion_pieceSeq ht hf hf' hB hker]
  apply Set.subset_iUnion _ j

theorem disjoint_pieceSeq [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (pieceSeq ht hf hf' hB hker i).E (pieceSeq ht hf hf' hB hker j).E := by
  wlog hlt : j < i
  · rw [disjoint_comm]
    apply disjoint_pieceSeq
    exact hij.symm
  rw [Set.disjoint_right]
  intro x hx
  apply Set.notMem_diff_of_mem
  simp only [Set.mem_iUnion, exists_prop]
  use j
  refine ⟨hlt, ?_⟩
  apply Set.mem_of_mem_of_subset hx
  apply Set.diff_subset

theorem LipschitzOnWith.euclideanHausdorffMeasure_image_le {X : Type*} {Y : Type*}
    [EMetricSpace X] [EMetricSpace Y] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    [BorelSpace Y] {K : NNReal} {f : X → Y} {s : Set X} (h : LipschitzOnWith K f s) {d : ℕ} :
    μHE[d] (f '' s) ≤ ↑K ^ d * μHE[d] s := by
  simp_rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [h.hausdorffMeasure_image_le (by simp)]
  rw [mul_left_comm]
  simp


/-theorem MeasureTheory.setLIntegral_mono_ae'₀ {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {s : Set α} {f g : α → ENNReal} (hs : NullMeasurableSet s μ)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ (x : α) in s, f x ∂μ ≤ ∫⁻ (x : α) in s, g x ∂μ := by
  rw [setLIntegral_congr hs.toMeasurable_ae_eq.symm, setLIntegral_congr hs.toMeasurable_ae_eq.symm]
  apply MeasureTheory.setLIntegral_mono_ae' (measurableSet_toMeasurable μ s)
  filter_upwards [hs.toMeasurable_ae_eq.mem_iff, hfg] with x hx h
  rwa [hx]-/

theorem area_left [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) (j : ℕ) :
    (↑t)⁻¹ ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' (pieceSeq ht hf hf' hB hker j).E) ≤
    ∫⁻ x in (pieceSeq ht hf hf' hB hker j).E, ENNReal.ofReal (f' x).normDet := by
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  calc
  _ = (↑t)⁻¹ ^ finrank ℝ U * (((↑t) ^ finrank ℝ U)⁻¹ *
      μHE[finrank ℝ U] ((f ∘ (pieceSeq ht hf hf' hB hker j).T.symm) ''
      (pieceSeq ht hf hf' hB hker j).T.toLinearMap '' (pieceSeq ht hf hf' hB hker j).E)) := by
    rw [← Set.image_comp]
    simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]
    rw [ENNReal.inv_pow]
    ring
  _ ≤ (↑t)⁻¹ ^ finrank ℝ U * volume ((pieceSeq ht hf hf' hB hker j).T.toLinearMap ''
      (pieceSeq ht hf hf' hB hker j).E) := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    rw [ENNReal.inv_mul_le_iff (by simp [ht0]) (by simp)]
    apply (pieceSeq ht hf hf' hB hker j).lipschitz.euclideanHausdorffMeasure_image_le
  _ = (↑t)⁻¹ ^ finrank ℝ U * ENNReal.ofReal |(pieceSeq ht hf hf' hB hker j).T.toLinearMap.det| *
      volume (pieceSeq ht hf hf' hB hker j).E := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, mul_assoc]
  _ ≤ _ := by
    rw [← MeasureTheory.setLIntegral_const]
    apply MeasureTheory.setLIntegral_mono_ae'
      ((pieceSeq ht hf hf' hB hker j).measurablSet ⟨hBm, hfm⟩)
    apply Filter.Eventually.of_forall
    intro x hx
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    simpa [LinearMap.normDet_nonneg] using (pieceSeq ht hf hf' hB hker j).det_le x hx

theorem area_right [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) (j : ℕ) :
    ∫⁻ x in (pieceSeq ht hf hf' hB hker j).E, ENNReal.ofReal (f' x).normDet ≤
    (↑t) ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' (pieceSeq ht hf hf' hB hker j).E) := by
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  calc
  _ ≤ (↑t) ^ finrank ℝ U * ENNReal.ofReal |(pieceSeq ht hf hf' hB hker j).T.toLinearMap.det| *
      volume (pieceSeq ht hf hf' hB hker j).E := by
    rw [← MeasureTheory.setLIntegral_const]
    apply MeasureTheory.setLIntegral_mono_ae'
      ((pieceSeq ht hf hf' hB hker j).measurablSet ⟨hBm, hfm⟩)
    apply Filter.Eventually.of_forall
    intro x hx
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    simpa [LinearMap.normDet_nonneg] using (pieceSeq ht hf hf' hB hker j).le_det x hx
  _ = (↑t) ^ finrank ℝ U * volume ((pieceSeq ht hf hf' hB hker j).T.toLinearMap ''
      (pieceSeq ht hf hf' hB hker j).E) := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, mul_assoc]
  _ = (↑t) ^ finrank ℝ U * μHE[finrank ℝ U] (((pieceSeq ht hf hf' hB hker j).T
      ∘ f.invFunOn (pieceSeq ht hf hf' hB hker j).E) '' f '' (pieceSeq ht hf hf' hB hker j).E) := by
    rw [Set.image_comp, Set.InjOn.invFunOn_image (hf.mono (by apply pieceSeq_subset))
      (subset_refl _), InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    simp
  _ ≤ (↑t) ^ finrank ℝ U * ((↑t) ^ finrank ℝ U *
      μHE[finrank ℝ U] (f '' (pieceSeq ht hf hf' hB hker j).E)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    apply (pieceSeq ht hf hf' hB hker j).lipschitz_inv.euclideanHausdorffMeasure_image_le
  _ ≤ _ := by
    apply le_of_eq
    ring

/-
--Aristotle
lemma Set.Infinite.iUnion_of_pairwise_disjoint {α ι : Type*} {s : ι → Set α}
    (hs : Pairwise (Function.onFun Disjoint s))
    (h : Set.Infinite {i | (s i).Nonempty}) : (⋃ i, s i).Infinite := by
  have h_choose : ∃ f : {i : ι | (s i).Nonempty} → α,
      ∀ i : {i : ι | (s i).Nonempty}, f i ∈ s i := by
    exact ⟨ fun i => Classical.choose i.2, fun i => Classical.choose_spec i.2 ⟩;
  obtain ⟨f, hf⟩ := h_choose;
  have h_distinct : Function.Injective f := by
    intro i j hij; have := hs;
    simp only [coe_setOf, mem_setOf_eq, Subtype.forall] at hf
    exact Subtype.ext ( Classical.not_not.1 fun hi => Set.disjoint_left.1
      ( this hi ) ( hf _ i.2 ) ( hij.symm ▸ hf _ j.2 ) );
  have h_image_infinite : Set.Infinite (Set.range f) := by
    convert Set.infinite_range_of_injective h_distinct;
    exact Set.infinite_coe_iff.mpr h;
  exact h_image_infinite.mono fun x hx => by
    obtain ⟨ i, rfl ⟩ := hx;
    exact Set.mem_iUnion_of_mem _ ( hf i )


--Aristotle
lemma Set.encard_biUnion_finset {α ι : Type*} {s : ι → Set α}
    (hs : Pairwise (Function.onFun Disjoint s))
    (t : Finset ι) :
    (⋃ i ∈ t, s i).encard = ∑ i ∈ t, (s i).encard := by
  classical
  induction t using Finset.induction with --with i t hi ih;
  | empty => simp
  | insert i t hi ih =>
    simp_all only [Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert];
    rw [ ← ih, Set.encard_union_eq ];
    exact Set.disjoint_iUnion₂_right.mpr fun j hj => hs ( by aesop )

--Aristotle
lemma ENat.tsum_eq_top_of_ne_zero {ι : Type*} {f : ι → ℕ∞}
    (h : Set.Infinite {i | f i ≠ 0}) : ∑' i, f i = ⊤ := by
  by_contra h_ne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∑' i, f i = n := by
    cases h_val : ∑' i, f i with
    | top => exact absurd h_val h_ne
    | coe n => exact ⟨n, rfl⟩
  obtain ⟨s, hs_sub, hs_card⟩ := h.exists_subset_card_eq (n + 1)
  have h1 : (↑(n + 1) : ℕ∞) ≤ ∑ i ∈ s, f i := by
    rw [← hs_card, Finset.card_eq_sum_ones]; push_cast
    exact Finset.sum_le_sum fun i hi => ENat.one_le_iff_ne_zero.mpr (hs_sub hi)
  have h_summ : Summable f := ⟨_, hasSum_of_isLUB _ isLUB_iSup⟩
  have h2 : ∑ i ∈ s, f i ≤ ∑' i, f i :=
    h_summ.sum_le_tsum s (fun i _ => zero_le)
  have h3 : (↑(n + 1) : ℕ∞) ≤ ↑n := h1.trans (h2.trans hn.le)
  exact absurd h3 (by exact_mod_cast Nat.lt_irrefl n)

--Aristotle
lemma ENat.le_tsum {ι : Type*} (f : ι → ℕ∞) (i : ι) : f i ≤ ∑' j, f j :=
  Summable.le_tsum' ⟨_, hasSum_of_isLUB _ isLUB_iSup⟩ i

--Aristotle
theorem Set.encard_iUnion {α : Type*} {ι : Type*} {s : ι → Set α}
    (hs : Pairwise (Function.onFun Disjoint s)) :
    (⋃ (i : ι), s i).encard = ∑' (i : ι), (s i).encard := by
  by_cases h_some_inf : ∃ i, (s i).Infinite
  · -- Case 1: Some s i is infinite
    obtain ⟨i, hi⟩ := h_some_inf
    have h1 : (⋃ j, s j).Infinite := hi.mono (Set.subset_iUnion s i)
    have h2 : (s i).encard = ⊤ := Set.encard_eq_top_iff.mpr hi
    rw [Set.encard_eq_top_iff.mpr h1]
    have : ∑' j, (s j).encard ≥ (s i).encard := ENat.le_tsum _ i
    rw [h2] at this
    exact (top_le_iff.mp this).symm
  · push Not at h_some_inf
    by_cases h_fin_support : Set.Finite {i | (s i).Nonempty}
    · -- Case 3: finitely many nonempty sets
      have h_zero : ∀ i, i ∉ h_fin_support.toFinset → (s i).encard = 0 := by
        intro i hi
        simp only [Finite.mem_toFinset, mem_setOf_eq] at hi
        exact Set.encard_eq_zero.mpr (Set.not_nonempty_iff_eq_empty.mp hi)
      rw [tsum_eq_sum h_zero]
      have h_eq : (⋃ i, s i) = ⋃ i ∈ h_fin_support.toFinset, s i := by
        ext x; simp [Set.Finite.mem_toFinset]
      rw [h_eq]
      exact Set.encard_biUnion_finset hs _
    · -- Case 2: infinitely many nonempty, all finite
      have h_inf_union : (⋃ i, s i).Infinite :=
        Set.Infinite.iUnion_of_pairwise_disjoint hs h_fin_support
      rw [Set.encard_eq_top_iff.mpr h_inf_union]
      have : Set.Infinite {i | (s i).encard ≠ 0} := by
        rwa [show {i | (s i).encard ≠ 0} = {i | (s i).Nonempty} from by
          ext i; exact Set.encard_ne_zero]
      exact (ENat.tsum_eq_top_of_ne_zero this).symm

theorem ENat.hasSum {α : Type u_1} {f : α → ENat} :
    HasSum f (⨆ (s : Finset α), ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

theorem ENat.summable {α : Type u_1} {f : α → ENat} :
    Summable f :=
  ENat.hasSum.summable

-- Aristotle
theorem continuous_ENat_toENNReal : Continuous ENat.toENNReal := by
  refine continuous_iff_continuousAt.2 fun x => ?_;
  induction x using WithTop.recTopCoe with
  | top =>
    refine ENNReal.tendsto_nhds_top ?_;
    intro n;
    rw [ eventually_nhds_iff ];
    use Set.Ioi (n : ENat);
    simp only [Set.mem_Ioi, isOpen_iff_mem_nhds];
    exact ⟨ fun y hy => by cases y <;> aesop,
    fun x hx => IsOpen.mem_nhds ( isOpen_Ioi ) hx, by exact WithTop.coe_lt_top _ ⟩;
  | coe a =>
    simp only [ContinuousAt, ENat.some_eq_coe];
    rw [ ENat.nhds_eq_pure ];
    · exact pure_le_nhds _;
    · exact ENat.coe_ne_top _-/

theorem glue_j [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    ∫⁻ x in B, ENNReal.ofReal (f' x).normDet =
    ∑' j, ∫⁻ x in (pieceSeq ht hf hf' hB hker j).E, ENNReal.ofReal (f' x).normDet := by
  conv_lhs => rw [iUnion_pieceSeq ht hf hf' hB hker]
  apply MeasureTheory.lintegral_iUnion
  · intro i
    apply Piece.measurablSet _ ⟨hBm, hfm⟩
  · intro i j h
    rw [Function.onFun]
    exact disjoint_pieceSeq ht hf hf' hB hker h

theorem μHE_image_zero [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V]
    {B : Set U} {f : U → V} {f' : U → U →L[ℝ] V}
    (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hs : volume B = 0)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    μHE[finrank ℝ U] (f '' B) = 0 := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · simp [hB]
  have hrank : 0 < finrank ℝ U := Module.finrank_pos
  have hrank' : 0 < 2 * finrank ℝ U := by simpa using hrank
  apply le_antisymm
  · have ht : (1 : NNReal) < (2 : NNReal) := by norm_num
    suffices 2⁻¹ ^ (finrank ℝ U) * μHE[finrank ℝ U] (f '' B) ≤ 0  by
      simpa
    calc
    _ = 2⁻¹ ^ (finrank ℝ U) * μHE[finrank ℝ U] (f ''
        ⋃ k, (pieceSeq ht hf hf' hB hker k).E) := by
      rw [← iUnion_pieceSeq ht]
    _ = 2⁻¹ ^ (finrank ℝ U) * μHE[finrank ℝ U] (
        ⋃ k, f '' (pieceSeq ht hf hf' hB hker k).E) := by
      rw [Set.image_iUnion]
    _ ≤ 2⁻¹ ^ (finrank ℝ U) * ∑' k, μHE[finrank ℝ U] (
        f '' (pieceSeq ht hf hf' hB hker k).E) := by
      grw [MeasureTheory.measure_iUnion_le]
    _ = ∑' k, 2⁻¹ ^ (finrank ℝ U) * μHE[finrank ℝ U] (
        f '' (pieceSeq ht hf hf' hB hker k).E) := by
      rw [ENNReal.tsum_mul_left]
    _ = ∑' k, (2 ^ (finrank ℝ U))⁻¹ *
        μHE[finrank ℝ U] ((f ∘ (pieceSeq ht hf hf' hB hker k).T.symm) ''
        (pieceSeq ht hf hf' hB hker k).T.toLinearMap ''
        (pieceSeq ht hf hf' hB hker k).E) := by
      congr with k
      rw [← Set.image_comp]
      simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]
      rw [ENNReal.inv_pow]
    _ ≤ ∑' k, volume ((pieceSeq ht hf hf' hB hker k).T.toLinearMap ''
        (pieceSeq ht hf hf' hB hker k).E) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      rw [ENNReal.inv_mul_le_iff (by simp) (by simp)]
      apply (pieceSeq ht hf hf' hB hker k).lipschitz.euclideanHausdorffMeasure_image_le
    _ = ∑' k, ENNReal.ofReal |(pieceSeq ht hf hf' hB hker k).T.toLinearMap.det| *
        volume (pieceSeq ht hf hf' hB hker k).E := by
      congr with k
      rw [MeasureTheory.Measure.addHaar_image_linearMap]
    _ ≤ ∑' k, ENNReal.ofReal |(pieceSeq ht hf hf' hB hker k).T.toLinearMap.det| *
        volume B := by
      apply ENNReal.tsum_le_tsum
      intro k
      gcongr
      conv_rhs => rw [iUnion_pieceSeq ht hf hf' hB hker]
      apply Set.subset_iUnion _ k
    _ = 0 := by simp [hs]
  · simp

theorem glue [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    μHE[finrank ℝ U] (f '' B) = ∑' j, μHE[finrank ℝ U] (f '' (pieceSeq ht hf hf' hB hker j).E) := by
  conv_lhs =>
    rw [iUnion_pieceSeq ht hf hf' hB hker]
    rw [Set.image_iUnion]
  apply measure_iUnion
  · intro j k h
    rw [Function.onFun]
    apply Disjoint.image ?_ hf (pieceSeq_subset ..) (pieceSeq_subset ..)
    apply disjoint_pieceSeq
    exact h
  · intro j
    apply MeasurableSet.image_of_continuousOn_injOn
      ((pieceSeq ht hf hf' hB hker j).measurablSet ⟨hBm, hfm⟩) ?_
      (hf.mono (pieceSeq_subset ..))
    intro x hx
    apply (hf' x (Set.mem_of_mem_of_subset hx (pieceSeq_subset ..))).continuousWithinAt.mono
    apply pieceSeq_subset


theorem left [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    ∫⁻ (x : U) in B, ENNReal.ofReal (f' x).normDet ≤
    ↑t ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' B) := by
  rw [glue_j ht hf hf' hBm hfm hB hker, glue ht hf hf' hBm hfm hB hker]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  apply area_right ht hf hf' hBm hfm hB hker

theorem right [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V]
    [CompleteSpace V] {t : NNReal} (ht : 1 < t) {f : U → V} {f' : U → U →L[ℝ] V}
    {B : Set U} (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x)
    (hBm : MeasurableSet B) (hfm : Measurable f')
    (hB : B.Nonempty)
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    (↑t)⁻¹ ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' B) ≤
    ∫⁻ (x : U) in B, ENNReal.ofReal (f' x).normDet := by
  rw [glue_j ht hf hf' hBm hfm hB hker, glue ht hf hf' hBm hfm hB hker]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  apply area_left ht hf hf' hBm hfm hB hker



public theorem area_formula_injOn_ker_measurable {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [Nontrivial U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {B : Set U} (hBm : MeasurableSet B)
    (hf : Set.InjOn f B) (hf' : ∀ x ∈ B, HasFDerivWithinAt f (f' x) B x) (hfm : Measurable f')
    (hker : ∀ x ∈ B, (f' x).ker = ⊥) :
    ∫⁻ x in B, ENNReal.ofReal (f' x).normDet = μHE[finrank ℝ U] (f '' B) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · simp [hB]
  have hrank : 0 < finrank ℝ U := Module.finrank_pos
  have hrank' : 0 < 2 * finrank ℝ U := by simpa using hrank
  suffices ∫⁻ x in B, ENNReal.ofReal (f' x).normDet =
      1 * μHE[finrank ℝ U] (f '' B) by
    simpa
  apply le_antisymm
  · suffices ∀ t : ENNReal, 1 < t → ∫⁻ x in B, ENNReal.ofReal (f' x).normDet ≤
        t ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' B) by
      apply ENNReal.le_mul_of_forall_lt (by simp) (by simp)
      intro a ha b hb
      refine le_trans (this (a ^ (((2 * finrank ℝ U : Nat) : Real)⁻¹)) ?_) ?_
      · apply ENNReal.one_lt_rpow (by simpa using ha)
        simpa using hrank
      · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ (by simpa using hrank.ne'), ENNReal.rpow_one]
        grw [hb]
    intro t
    induction t using ENNReal.recTopCoe with
    | top =>
      intro ht
      by_cases h0 : μHE[finrank ℝ U] (f '' B) = 0
      · have h := left (show 1 < 2 by simp) hf hf' hBm hfm hB hker
        simp_all
      simp [hrank.ne', h0]
    | coe t =>
      intro ht
      norm_cast at ht
      apply left ht hf hf' hBm hfm hB hker
  · suffices ∀ t : ENNReal, 1 < t → t⁻¹ ^ (2 * finrank ℝ U) * μHE[finrank ℝ U] (f '' B) ≤
        ∫⁻ x in B, ENNReal.ofReal (f' x).normDet by
      apply ENNReal.mul_le_of_forall_lt
      intro a ha b hb
      refine le_trans ?_ (this (a ^ (-((2 * finrank ℝ U : Nat) : Real)⁻¹)) ?_)
      · rw [← ENNReal.rpow_natCast, ← ENNReal.inv_rpow, ← ENNReal.rpow_mul,
          neg_mul, inv_mul_cancel₀ (by simpa using hrank.ne'), ENNReal.rpow_neg_one,
          inv_inv]
        grw [hb]
      · rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow]
        apply ENNReal.one_lt_rpow (by simpa using ha)
        simpa using hrank
    intro t
    induction t using ENNReal.recTopCoe with
    | top => simp [hrank.ne']
    | coe t =>
      intro ht
      norm_cast at ht
      apply right ht hf hf' hBm hfm hB hker


public theorem area_formula_injOn_ker {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [Nontrivial U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U} (hs : MeasurableSet s)
    (hf : Set.InjOn f s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hker : ∀ x ∈ s, (f' x).ker = ⊥) :
    ∫⁻ x in s, ENNReal.ofReal (f' x).normDet = μHE[finrank ℝ U] (f '' s) := by
  obtain ⟨g, hgm, hfg⟩ := aemeasurable_fderivWithin volume hs hf'
  let t := {x | x ∈ s ∧ f' x ≠ g x}
  obtain hfg' := MeasureTheory.ae_iff.mp <| (MeasureTheory.ae_restrict_iff' hs).mp hfg
  have ht : volume t = 0 := by
    apply eq_zero_of_nonpos
    rw [← hfg']
    apply measure_mono
    simp [t]
  obtain ⟨u, htu, hmu, hu⟩ := MeasureTheory.exists_measurable_superset_iff_measure_eq_zero.mpr ht
  have hfu : μHE[finrank ℝ U] (f '' (s ∩ u)) = 0 := by
    apply μHE_image_zero (hf.mono Set.inter_subset_left) (fun x hx ↦
      (hf' x (Set.mem_of_mem_of_subset hx Set.inter_subset_left)).mono Set.inter_subset_left) ?_ ?_
    · apply eq_zero_of_nonpos
      rw [← hu]
      apply measure_mono
      exact Set.inter_subset_right
    · intro x hx
      exact hker x (Set.mem_of_mem_of_subset hx Set.inter_subset_left)
  calc
  _ = ∫⁻ x in (s \ u), ENNReal.ofReal (f' x).normDet := by
    apply MeasureTheory.setLIntegral_congr
    symm
    apply MeasureTheory.diff_null_ae_eq_self hu
  _ = ∫⁻ x in (s \ u), ENNReal.ofReal (g x).normDet := by
    apply MeasureTheory.setLIntegral_congr_fun_ae (hs.diff hmu)
    rw [← MeasureTheory.ae_restrict_iff' (hs.diff hmu)]
    suffices f' =ᵐ[volume.restrict (s \ u)] g by
      exact Filter.EventuallyEq.fun_comp this
        (fun x ↦ ENNReal.ofReal (LinearMap.normDet x.toLinearMap))
    apply Filter.EventuallyEq.filter_mono hfg
    apply MeasureTheory.ae_mono
    exact MeasureTheory.Measure.restrict_mono Set.diff_subset le_rfl
  _ = μHE[finrank ℝ U] (f '' (s \ u)) := by
    refine area_formula_injOn_ker_measurable (hs.diff hmu) (hf.mono Set.diff_subset)
      (fun x hx ↦ ?_) hgm (fun x hx ↦ ?_)
    <;> have hx' : x ∈ (s \ t) := by
          apply Set.mem_of_mem_of_subset hx
          gcongr
    · obtain ⟨hxs, hf'g⟩ : x ∈ s ∧ f' x = g x := by simpa [t] using hx'
      rw [← hf'g]
      exact (hf' x hxs).mono Set.diff_subset
    · obtain ⟨hxs, hf'g⟩ : x ∈ s ∧ f' x = g x := by simpa [t] using hx'
      rw [← hf'g]
      apply hker x hxs
  _ = μHE[finrank ℝ U] (f '' (s \ u)) + μHE[finrank ℝ U] (f '' (s ∩ u))
      - μHE[finrank ℝ U] (f '' (s ∩ u)) := by
    rw [ENNReal.add_sub_cancel_right (by simp [hfu])]
  _ = _ := by
    rw [← measure_union (Disjoint.image (by grind) hf Set.diff_subset Set.inter_subset_left) ?_,
      ← Set.image_union, Set.diff_union_inter, hfu, tsub_zero]
    refine MeasurableSet.image_of_continuousOn_injOn (hs.inter hmu) ?_
      (hf.mono Set.inter_subset_left)
    intro x hx
    apply (hf' x (Set.mem_of_mem_of_subset hx Set.inter_subset_left)).continuousWithinAt.mono
      Set.inter_subset_left



/-
theorem area_sphere : μHE[2] (Metric.sphere 0 1 : Set (EuclideanSpace ℝ (Fin 3))) = sorry := by
  let s := (Metric.sphere 0 1 : Set (EuclideanSpace ℝ (Fin 3))) \
      ({!₂[0, 0, 1], !₂[0, 0, -1]})
  have hremove_points : μHE[2] (Metric.sphere 0 1 : Set (EuclideanSpace ℝ (Fin 3))) =
      μHE[finrank ℝ (EuclideanSpace ℝ (Fin 2))] s := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    apply (MeasureTheory.measure_diff_null ?_).symm
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
    simp only [Nat.cast_ofNat, Measure.smul_apply, Measure.nnreal_smul_coe_apply, mul_eq_zero,
      ENNReal.coe_eq_zero]
    right
    suffices μH[(2 : NNReal)] ({!₂[0, 0, 1], !₂[0, 0, -1]} : Set (EuclideanSpace ℝ (Fin 3))) = 0 by
      simpa
    apply hausdorffMeasure_of_dimH_lt
    rw [dimH_countable (by simp)]
    simp
  let f (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
    !₂[Real.cos (p 0) * Real.cos (p 1), Real.cos (p 0) * Real.sin (p 1), Real.sin (p 0)]
  have hfderiv (p : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ f p = (Matrix.toEuclideanLin
      !![-Real.sin (p 0) * Real.cos (p 1), -Real.cos (p 0) * Real.sin (p 1);
         -Real.sin (p 0) * Real.sin (p 1), Real.cos (p 0) * Real.cos (p 1);
         Real.cos (p 0), 0]
      ).toContinuousLinearMap := by
    ext v i
    fin_cases i
    · simp [f]
      sorry
    · sorry
    · sorry

  let t : Set (EuclideanSpace ℝ (Fin 2)) := WithLp.toLp 2 ''
    (Set.univ.pi ![Set.Ioo (-Real.pi / 2) (Real.pi / 2), Set.Ico 0 (2 * Real.pi)])

  have hmap : s = f '' t := sorry
  have hinj : Set.InjOn f t := sorry
  rw [hremove_points, hmap, area_formula_injective sorry sorry hinj]

  sorry
-/
