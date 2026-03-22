/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convolution

/-!
# Differentiability of a convolution of functions

Criteria for a convolution of functions to be differentiable.

## Main Results

* `HasCompactSupport.hasFDerivAt_convolution_right` and
  `HasCompactSupport.hasFDerivAt_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `HasCompactSupport.contDiff_convolution_right` and
  `HasCompactSupport.contDiff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.

-/

@[expose] public section
open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open Bornology ContinuousLinearMap Metric Topology
open scoped Pointwise NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

namespace MeasureTheory
section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]
variable (L : E →L[𝕜] E' →L[𝕜] F)

end NontriviallyNormedField

open scoped Convolution

section RCLike
variable [RCLike 𝕜]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 E']
variable [NormedSpace 𝕜 E'']
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable {n : ℕ∞}
variable [MeasurableSpace G] {μ ν : Measure G}
variable (L : E →L[𝕜] E' →L[𝕜] F)

variable [NormedAddCommGroup G] [BorelSpace G]

variable [NormedSpace 𝕜 G] [SFinite μ] [IsAddLeftInvariant μ]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`ContinuousLinearMap.precompR`. -/
theorem _root_.HasCompactSupport.hasFDerivAt_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 1 g) (x₀ : G) :
    HasFDerivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ := by
  rcases hcg.eq_zero_or_finiteDimensional 𝕜 hg.continuous with (rfl | fin_dim)
  · have : fderiv 𝕜 (0 : G → E') = 0 := fderiv_const (0 : E')
    simp only [this, convolution_zero, Pi.zero_apply]
    exact hasFDerivAt_const (0 : F) x₀
  have : ProperSpace G := FiniteDimensional.proper_rclike 𝕜 G
  set L' := L.precompR G
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
    Eventually.of_forall
      (hf.aestronglyMeasurable.convolution_integrand_snd L hg.continuous.aestronglyMeasurable)
  have h2 : ∀ x, AEStronglyMeasurable (fun t => L' (f t) (fderiv 𝕜 g (x - t))) μ :=
    hf.aestronglyMeasurable.convolution_integrand_snd L'
      (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have h3 : ∀ x t, HasFDerivAt (fun x => g (x - t)) (fderiv 𝕜 g (x - t)) x := fun x t ↦ by
    simpa using
      (hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
  let K' := -tsupport (fderiv 𝕜 g) + closedBall x₀ 1
  have hK' : IsCompact K' := (hcg.fderiv 𝕜).isCompact.neg.add (isCompact_closedBall x₀ 1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds _ zero_lt_one) h1 _ (h2 x₀)
  · filter_upwards with t x hx using
      (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv one_ne_zero)
        (ball_subset_closedBall hx)
  · rw [integrable_indicator_iff hK'.measurableSet]
    exact ((hf.integrableOn_isCompact hK').norm.const_mul _).mul_const _
  · exact Eventually.of_forall fun t x _ => (L _).hasFDerivAt.comp x (h3 x t)
  · exact hcg.convolutionExists_right L hf hg.continuous x₀

theorem _root_.HasCompactSupport.hasFDerivAt_convolution_left [IsNegInvariant μ]
    (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 1 f) (hg : LocallyIntegrable g μ) (x₀ : G) :
    HasFDerivAt (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ := by
  simp +singlePass only [← convolution_flip]
  exact hcf.hasFDerivAt_convolution_right L.flip hg hf x₀

end RCLike

section Real

/-! The one-variable case -/

variable [RCLike 𝕜]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 E']
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}
variable {n : ℕ∞}
variable (L : E →L[𝕜] E' →L[𝕜] F)
variable {μ : Measure 𝕜}
variable [IsAddLeftInvariant μ] [SFinite μ]

theorem _root_.HasCompactSupport.hasDerivAt_convolution_right (hf : LocallyIntegrable f₀ μ)
    (hcg : HasCompactSupport g₀) (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ := by
  convert (hcg.hasFDerivAt_convolution_right L hf hg x₀).hasDerivAt using 1
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv one_ne_zero)]
  rfl

theorem _root_.HasCompactSupport.hasDerivAt_convolution_left [IsNegInvariant μ]
    (hcf : HasCompactSupport f₀) (hf : ContDiff 𝕜 1 f₀) (hg : LocallyIntegrable g₀ μ) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ := by
  simp +singlePass only [← convolution_flip]
  exact hcf.hasDerivAt_convolution_right L.flip hg hf x₀

end Real

section WithParam

variable [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedAddCommGroup G] [BorelSpace G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P] {μ : Measure G}
  (L : E →L[𝕜] E' →L[𝕜] F)

/-- The derivative of the convolution `f * g` is given by `f * Dg`, when `f` is locally integrable
and `g` is `C^1` and compactly supported. Version where `g` depends on an additional parameter in an
open subset `s` of a parameter space `P` (and the compact support `k` is independent of the
parameter in `s`). -/
theorem hasFDerivAt_convolution_right_with_param {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 1 ↿g (s ×ˢ univ)) (q₀ : P × G)
    (hq₀ : q₀.1 ∈ s) :
    HasFDerivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2)
      ((f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 ↿g (q₀.1, x)) q₀.2) q₀ := by
  let g' := fderiv 𝕜 ↿g
  have A : ∀ p ∈ s, Continuous (g p) := fun p hp ↦ by
    refine hg.continuousOn.comp_continuous (.prodMk_right _) fun x => ?_
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
  have A' : ∀ q : P × G, q.1 ∈ s → s ×ˢ univ ∈ 𝓝 q := fun q hq ↦ by
    apply (hs.prod isOpen_univ).mem_nhds
    simpa only [mem_prod, mem_univ, and_true] using hq
  -- The derivative of `g` vanishes away from `k`.
  have g'_zero : ∀ p x, p ∈ s → x ∉ k → g' (p, x) = 0 := by
    intro p x hp hx
    refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have M2 : kᶜ ∈ 𝓝 x := hk.isClosed.isOpen_compl.mem_nhds hx
    have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod M1 M2]
    rintro ⟨p, y⟩ ⟨hp, hy⟩
    exact hgs p y hp hy
  /- We find a small neighborhood of `{q₀.1} × k` on which the derivative is uniformly bounded. This
    follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨ε, C, εpos, h₀ε, hε⟩ :
      ∃ ε C, 0 < ε ∧ ball q₀.1 ε ⊆ s ∧ ∀ p x, ‖p - q₀.1‖ < ε → ‖g' (p, x)‖ ≤ C := by
    have A : IsCompact ({q₀.1} ×ˢ k) := isCompact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ : ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ IsOpen t ∧ IsBounded (g' '' t) := by
      have B : ContinuousOn g' (s ×ˢ univ) :=
        hg.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) le_rfl
      apply exists_isOpen_isBounded_image_of_isCompact_of_continuousOn A (hs.prod isOpen_univ) _ B
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or]
    obtain ⟨ε, εpos, hε, h'ε⟩ :
      ∃ ε : ℝ, 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t ∧ ball q₀.1 ε ⊆ s := by
      obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ thickening ε (({q₀.fst} : Set P) ×ˢ k) ⊆ t :=
        A.exists_thickening_subset_open t_open kt
      obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ball q₀.1 δ ⊆ s := Metric.isOpen_iff.1 hs _ hq₀
      refine ⟨min ε δ, lt_min εpos δpos, ?_, ?_⟩
      · exact Subset.trans (thickening_mono (min_le_left _ _) _) hε
      · exact Subset.trans (ball_subset_ball (min_le_right _ _)) hδ
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ g' '' t ⊆ closedBall 0 C := ht.subset_closedBall_lt 0 0
    refine ⟨ε, C, εpos, h'ε, fun p x hp => ?_⟩
    have hps : p ∈ s := h'ε (mem_ball_iff_norm.2 hp)
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hε
        refine mem_thickening_iff.2 ⟨(q₀.1, x), ?_, ?_⟩
        · simp only [hx, singleton_prod, mem_image, Prod.mk_inj, true_and, exists_eq_right]
        · rw [← dist_eq_norm] at hp
          simpa only [Prod.dist_eq, εpos, dist_self, max_lt_iff, and_true] using hp
      have : g' (p, x) ∈ closedBall (0 : P × G →L[𝕜] E') C := hC (mem_image_of_mem _ H)
      rwa [mem_closedBall_zero_iff] at this
    · have : g' (p, x) = 0 := g'_zero _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  /- Now, we wish to apply a theorem on differentiation of integrals. For this, we need to check
    trivial measurability or integrability assumptions (in `I1`, `I2`, `I3`), as well as a uniform
    integrability assumption over the derivative (in `I4` and `I5`) and pointwise differentiability
    in `I6`. -/
  have I1 :
    ∀ᶠ x : P × G in 𝓝 q₀, AEStronglyMeasurable (fun a : G => L (f a) (g x.1 (x.2 - a))) μ := by
    filter_upwards [A' q₀ hq₀]
    rintro ⟨p, x⟩ ⟨hp, -⟩
    refine (HasCompactSupport.convolutionExists_right L ?_ hf (A _ hp) _).1
    apply hk.of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) hk.isClosed
  have I2 : Integrable (fun a : G => L (f a) (g q₀.1 (q₀.2 - a))) μ := by
    have M : HasCompactSupport (g q₀.1) := HasCompactSupport.intro hk fun x hx => hgs q₀.1 x hq₀ hx
    apply M.convolutionExists_right L hf (A q₀.1 hq₀) q₀.2
  have I3 : AEStronglyMeasurable (fun a : G => (L (f a)).comp (g' (q₀.fst, q₀.snd - a))) μ := by
    have T : HasCompactSupport fun y => g' (q₀.1, y) :=
      HasCompactSupport.intro hk fun x hx => g'_zero q₀.1 x hq₀ hx
    apply (HasCompactSupport.convolutionExists_right (L.precompR (P × G) :) T hf _ q₀.2).1
    have : ContinuousOn g' (s ×ˢ univ) :=
      hg.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) le_rfl
    apply this.comp_continuous (.prodMk_right _)
    intro x
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hq₀
  set K' := (-k + {q₀.2} : Set G) with K'_def
  have hK' : IsCompact K' := hk.neg.add isCompact_singleton
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ IntegrableOn f U μ :=
    hf.integrableOn_nhds_isCompact hK'
  obtain ⟨δ, δpos, δε, hδ⟩ : ∃ δ, (0 : ℝ) < δ ∧ δ ≤ ε ∧ K' + ball 0 δ ⊆ U := by
    obtain ⟨V, V_mem, hV⟩ : ∃ V ∈ 𝓝 (0 : G), K' + V ⊆ U :=
      compact_open_separated_add_right hK' U_open K'U
    rcases Metric.mem_nhds_iff.1 V_mem with ⟨δ, δpos, hδ⟩
    refine ⟨min δ ε, lt_min δpos εpos, min_le_right δ ε, ?_⟩
    exact (add_subset_add_left ((ball_subset_ball (min_le_left _ _)).trans hδ)).trans hV
  letI := ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜) (E := E)
    (F := (P × G →L[𝕜] E') →L[𝕜] P × G →L[𝕜] F) (σ₁₂ := RingHom.id 𝕜)
  let bound : G → ℝ := indicator U fun t => ‖(L.precompR (P × G))‖ * ‖f t‖ * C
  have I4 : ∀ᵐ a : G ∂μ, ∀ x : P × G, dist x q₀ < δ →
      ‖L.precompR (P × G) (f a) (g' (x.fst, x.snd - a))‖ ≤ bound a := by
    filter_upwards with a x hx
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hx
    have : (-tsupport fun a => g' (x.1, a)) + ball q₀.2 δ ⊆ U := by
      apply Subset.trans _ hδ
      rw [K'_def, add_assoc]
      apply add_subset_add
      · rw [neg_subset_neg]
        refine closure_minimal (support_subset_iff'.2 fun z hz => ?_) hk.isClosed
        apply g'_zero x.1 z (h₀ε _) hz
        rw [mem_ball_iff_norm]
        exact ((le_max_left _ _).trans_lt hx).trans_le δε
      · simp only [add_ball, thickening_singleton, zero_vadd, subset_rfl]
    apply convolution_integrand_bound_right_of_le_of_subset _ _ _ this
    · intro y
      exact hε _ _ (((le_max_left _ _).trans_lt hx).trans_le δε)
    · rw [mem_ball_iff_norm]
      exact (le_max_right _ _).trans_lt hx
  have I5 : Integrable bound μ := by
    rw [integrable_indicator_iff U_open.measurableSet]
    exact (hU.norm.const_mul _).mul_const _
  have I6 : ∀ᵐ a : G ∂μ, ∀ x : P × G, dist x q₀ < δ →
      HasFDerivAt (fun x : P × G => L (f a) (g x.1 (x.2 - a)))
        ((L (f a)).comp (g' (x.fst, x.snd - a))) x := by
    filter_upwards with a x hx
    apply (L _).hasFDerivAt.comp x
    have N : s ×ˢ univ ∈ 𝓝 (x.1, x.2 - a) := by
      apply A'
      apply h₀ε
      rw [Prod.dist_eq] at hx
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hx) δε
    have Z := ((hg.differentiableOn one_ne_zero).differentiableAt N).hasFDerivAt
    have Z' :
        HasFDerivAt (fun x : P × G => (x.1, x.2 - a)) (ContinuousLinearMap.id 𝕜 (P × G)) x := by
      have : (fun x : P × G => (x.1, x.2 - a)) = _root_.id - fun x => (0, a) := by
        ext x <;> simp only [Pi.sub_apply, _root_.id, Prod.fst_sub, sub_zero, Prod.snd_sub]
      rw [this]
      exact (hasFDerivAt_id x).sub_const (0, a)
    exact Z.comp x Z'
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds _ δpos) I1 I2 I3 I4 I5 I6

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`).
In this version, all the types belong to the same universe (to get an induction working in the
proof). Use instead `contDiffOn_convolution_right_with_param`, which removes this restriction. -/
theorem contDiffOn_convolution_right_with_param_aux {G : Type uP} {E' : Type uP} {F : Type uP}
    {P : Type uP} [NormedAddCommGroup E'] [NormedAddCommGroup F] [NormedSpace 𝕜 E']
    [NormedSpace ℝ F] [NormedSpace 𝕜 F] [MeasurableSpace G]
    {μ : Measure G}
    [NormedAddCommGroup G] [BorelSpace G] [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- We have a formula for the derivation of `f * g`, which is of the same form, thanks to
    `hasFDerivAt_convolution_right_with_param`. Therefore, we can prove the result by induction on
    `n` (but for this we need the spaces at the different steps of the induction to live in the same
    universe, which is why we make the assumption in the lemma that all the relevant spaces
    come from the same universe). -/
  induction n using ENat.nat_induction generalizing g E' F with
  | zero =>
    rw [WithTop.coe_zero, contDiffOn_zero] at hg ⊢
    exact continuousOn_convolution_right_with_param L hk hgs hf hg
  | succ n ih =>
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, WithTop.coe_add,
      WithTop.coe_natCast, WithTop.coe_one] at hg ⊢
    let f' : P → G → P × G →L[𝕜] F := fun p a =>
      (f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 (uncurry g) (p, x)) a
    have A : ∀ q₀ : P × G, q₀.1 ∈ s →
        HasFDerivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (f' q₀.1 q₀.2) q₀ :=
      hasFDerivAt_convolution_right_with_param L hs hk hgs hf hg.one_of_succ
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (hs.prod (@isOpen_univ G _))] at hg ⊢
    refine ⟨?_, by simp, ?_⟩
    · rintro ⟨p, x⟩ ⟨hp, -⟩
      exact (A (p, x) hp).differentiableAt.differentiableWithinAt
    · suffices H : ContDiffOn 𝕜 n ↿f' (s ×ˢ univ) by
        apply H.congr
        rintro ⟨p, x⟩ ⟨hp, -⟩
        exact (A (p, x) hp).fderiv
      have B : ∀ (p : P) (x : G), p ∈ s → x ∉ k → fderiv 𝕜 (uncurry g) (p, x) = 0 := by
        intro p x hp hx
        apply (hasFDerivAt_zero_of_eventually_const (0 : E') _).fderiv
        have M2 : kᶜ ∈ 𝓝 x := IsOpen.mem_nhds hk.isClosed.isOpen_compl hx
        have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
        rw [nhds_prod_eq]
        filter_upwards [prod_mem_prod M1 M2]
        rintro ⟨p, y⟩ ⟨hp, hy⟩
        exact hgs p y hp hy
      apply ih (L.precompR (P × G) :) B
      convert hg.2.2
  | top ih =>
    rw [contDiffOn_infty] at hg ⊢
    exact fun n ↦ ih n L hgs (hg n)

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem contDiffOn_convolution_right_with_param {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F)
    {g : P → G → E'} {s : Set P} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- The result is known when all the universes are the same, from
    `contDiffOn_convolution_right_with_param_aux`. We reduce to this situation by pushing
    everything through `ULift` continuous linear equivalences. -/
  let eG : Type max uG uE' uF uP := ULift.{max uE' uF uP} G
  borelize eG
  let eE' : Type max uE' uG uF uP := ULift.{max uG uF uP} E'
  let eF : Type max uF uG uE' uP := ULift.{max uG uE' uP} F
  let eP : Type max uP uG uE' uF := ULift.{max uG uE' uF} P
  let isoG : eG ≃L[𝕜] G := ContinuousLinearEquiv.ulift
  let isoE' : eE' ≃L[𝕜] E' := ContinuousLinearEquiv.ulift
  let isoF : eF ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  let isoP : eP ≃L[𝕜] P := ContinuousLinearEquiv.ulift
  let ef := f ∘ isoG
  let eμ : Measure eG := Measure.map isoG.symm μ
  let eg : eP → eG → eE' := fun ep ex => isoE'.symm (g (isoP ep) (isoG ex))
  let eL :=
    ContinuousLinearMap.comp
      ((ContinuousLinearEquiv.arrowCongr isoE' isoF).symm : (E' →L[𝕜] F) →L[𝕜] eE' →L[𝕜] eF) L
  let R := fun q : eP × eG => (ef ⋆[eL, eμ] eg q.1) q.2
  have R_contdiff : ContDiffOn 𝕜 n R ((isoP ⁻¹' s) ×ˢ univ) := by
    have hek : IsCompact (isoG ⁻¹' k) := isoG.toHomeomorph.isClosedEmbedding.isCompact_preimage hk
    have hes : IsOpen (isoP ⁻¹' s) := isoP.continuous.isOpen_preimage _ hs
    refine contDiffOn_convolution_right_with_param_aux eL hes hek ?_ ?_ ?_
    · intro p x hp hx
      simp only [eg,
        ContinuousLinearEquiv.map_eq_zero_iff]
      exact hgs _ _ hp hx
    · exact (locallyIntegrable_map_homeomorph isoG.symm.toHomeomorph).2 hf
    · apply isoE'.symm.contDiff.comp_contDiffOn
      apply hg.comp (isoP.prodCongr isoG).contDiff.contDiffOn
      rintro ⟨p, x⟩ ⟨hp, -⟩
      simpa only [mem_preimage, ContinuousLinearEquiv.prodCongr_apply, prodMk_mem_set_prod_eq,
        mem_univ, and_true] using hp
  have A : ContDiffOn 𝕜 n (isoF ∘ R ∘ (isoP.prodCongr isoG).symm) (s ×ˢ univ) := by
    apply isoF.contDiff.comp_contDiffOn
    apply R_contdiff.comp (ContinuousLinearEquiv.contDiff _).contDiffOn
    rintro ⟨p, x⟩ ⟨hp, -⟩
    simpa only [mem_preimage, mem_prod, mem_univ, and_true, ContinuousLinearEquiv.prodCongr_symm,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.apply_symm_apply] using hp
  have : isoF ∘ R ∘ (isoP.prodCongr isoG).symm = fun q : P × G => (f ⋆[L, μ] g q.1) q.2 := by
    apply funext
    rintro ⟨p, x⟩
    simp only [(· ∘ ·), ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply]
    simp only [R, convolution]
    rw [IsClosedEmbedding.integral_map, ← isoF.integral_comp_comm]
    · rfl
    · exact isoG.symm.toHomeomorph.isClosedEmbedding
  simp_rw [this] at A
  exact A

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with an additional `C^n` function. -/
theorem contDiffOn_convolution_right_with_param_comp {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {s : Set P}
    {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E} {g : P → G → E'} {k : Set G} (hs : IsOpen s)
    (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (f ⋆[L, μ] g x) (v x)) s := by
  apply (contDiffOn_convolution_right_with_param L hs hk hgs hf hg).comp (contDiffOn_id.prodMk hv)
  intro x hx
  simp only [hx, prodMk_mem_set_prod_eq, mem_univ, and_self_iff, _root_.id]

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem contDiffOn_convolution_left_with_param [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {f : G → E} {n : ℕ∞} {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (g q.1 ⋆[L, μ] f) q.2) (s ×ˢ univ) := by
  simpa only [convolution_flip] using contDiffOn_convolution_right_with_param L.flip hs hk hgs hf hg

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with additional `C^n` functions. -/
theorem contDiffOn_convolution_left_with_param_comp [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {s : Set P} {n : ℕ∞} {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E}
    {g : P → G → E'} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (g x ⋆[L, μ] f) (v x)) s := by
  apply (contDiffOn_convolution_left_with_param L hs hk hgs hf hg).comp (contDiffOn_id.prodMk hv)
  intro x hx
  simp only [hx, prodMk_mem_set_prod_eq, mem_univ, and_self_iff, _root_.id]

theorem _root_.HasCompactSupport.contDiff_convolution_right {n : ℕ∞} (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rcases exists_compact_iff_hasCompactSupport.2 hcg with ⟨k, hk, h'k⟩
  rw [← contDiffOn_univ]
  exact contDiffOn_convolution_right_with_param_comp L contDiffOn_id isOpen_univ hk
    (fun p x _ hx => h'k x hx) hf (hg.comp contDiff_snd).contDiffOn

theorem _root_.HasCompactSupport.contDiff_convolution_left [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {n : ℕ∞} (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 n f) (hg : LocallyIntegrable g μ) :
    ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.contDiff_convolution_right L.flip hg hf

end WithParam

end MeasureTheory
