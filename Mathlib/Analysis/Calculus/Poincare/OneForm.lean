/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
-/

open scoped unitInterval Interval Pointwise Topology
open Function Set MeasureTheory Filter
open AffineMap (lineMap)

instance Prod.instZeroLEOneClass {R S : Type*} [Zero R] [One R] [LE R] [ZeroLEOneClass R]
    [Zero S] [One S] [LE S] [ZeroLEOneClass S] : ZeroLEOneClass (R × S) :=
  ⟨⟨zero_le_one, zero_le_one⟩⟩

instance Pi.instZeroLEOneClass {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)] [∀ i, One (R i)]
    [∀ i, LE (R i)] [∀ i, ZeroLEOneClass (R i)] : ZeroLEOneClass (∀ i, R i) :=
  ⟨fun _ ↦ zero_le_one⟩

theorem HasFDerivWithinAt.comp_hasFDerivAt {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {g : F → G} {f : E → F} {s : Set F} (a : E)
    {g' : F →L[𝕜] G} {f' : E →L[𝕜] F} (hg : HasFDerivWithinAt g g' s (f a))
    (hf : HasFDerivAt f f' a) (hfs : ∀ᶠ x in 𝓝 a, f x ∈ s) : HasFDerivAt (g ∘ f) (g' ∘L f') a :=
  (hg.comp a hf.hasFDerivWithinAt (mapsTo_preimage f s)).hasFDerivAt hfs

@[simp]
theorem Path.extend_cast {X : Type*} [TopologicalSpace X] {x y x' y' : X} (γ : Path x y)
    (hx : x' = x) (hy : y' = y) : (γ.cast hx hy).extend = γ.extend := rfl

theorem Path.extend_trans_of_le_half {X : Type*} [TopologicalSpace X] {x y z : X} (γ₁ : Path x y)
    (γ₂ : Path y z) {t : ℝ} (ht : t ≤ 1 / 2) : (γ₁.trans γ₂).extend t = γ₁.extend (2 * t) := by
  cases le_total t 0 with
  | inl ht₀ => simp [Path.extend_of_le_zero, ht₀, mul_nonpos_of_nonneg_of_nonpos]
  | inr ht₀ => simp_all [extend_extends _ ⟨ht₀, by linarith⟩, Path.trans]

theorem Path.extend_trans_of_half_le {X : Type*} [TopologicalSpace X] {x y z : X} (γ₁ : Path x y)
    (γ₂ : Path y z) {t : ℝ} (ht : 1 / 2 ≤ t) : (γ₁.trans γ₂).extend t = γ₂.extend (2 * t - 1) := by
  conv_lhs => rw [← sub_sub_cancel 1 t]
  rw [← extend_symm_apply, trans_symm, extend_trans_of_le_half _ _ (by linarith), extend_symm_apply]
  congr 1
  linarith

@[to_additive]
theorem nhds_smul {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (g : G) (x : X) : 𝓝 (g • x) = g • 𝓝 x :=
  (Homeomorph.smul g).map_nhds_eq x |>.symm

@[to_additive]
theorem Filter.smul_principal {α β : Type*} [SMul α β] (a : α) (s : Set β) : a • 𝓟 s = 𝓟 (a • s) :=
  map_principal

@[to_additive]
theorem Filter.smul_filter_inf {G α : Type*} [Group G] [MulAction G α] (g : G) (l₁ l₂ : Filter α) :
    g • (l₁ ⊓ l₂) = g • l₁ ⊓ g • l₂ :=
  map_inf <| MulAction.injective g

theorem nhdsWithin_smul {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (g : G) (s : Set X) (x : X) : 𝓝[g • s] (g • x) = g • 𝓝[s] x := by
  simp only [nhdsWithin, smul_filter_inf, nhds_smul, smul_principal]

-- ContinuousLinearEquiv.comp_right_fderivWithin

theorem Set.Subsingleton.hasFDerivWithinAt {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {a : E} (hs : s.Subsingleton) :
    HasFDerivWithinAt f f' s a :=
  .of_subsingleton hs

theorem Set.Finite.fderivWithin_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : s.Finite) (f : E → F) : fderivWithin 𝕜 f s = 0 := by
  ext1 x
  simp [fderivWithin, HasFDerivWithinAt.of_finite hs]

theorem Set.Subsingleton.fderivWithin_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : s.Subsingleton) (f : E → F) : fderivWithin 𝕜 f s = 0 :=
  hs.finite.fderivWithin_eq f

theorem Set.Finite.derivWithin_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set 𝕜} (hs : s.Finite) (f : 𝕜 → E) :
    derivWithin f s = 0 := by
  ext1 x
  simp [derivWithin, hs.fderivWithin_eq]

theorem Set.Subsingleton.derivWithin_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set 𝕜} (hs : s.Subsingleton) (f : 𝕜 → E) :
    derivWithin f s = 0 :=
  hs.finite.derivWithin_eq f

theorem derivWithin_comp_mul_left {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (s : Set 𝕜) (a b : 𝕜) :
    derivWithin (f <| a * ·) s b = a • derivWithin f (a • s) (a * b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [s.subsingleton_zero_smul_set.derivWithin_eq]
  · lift a to 𝕜ˣ using IsUnit.mk0 a ha
    cases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s b with
    | inl hsb =>
      generalize ht : a.val • s = t
      set e : 𝕜 ≃L[𝕜] 𝕜 := ContinuousLinearEquiv.unitsEquivAut _ a
      have he : ∀ x, e x = a * x := fun _ ↦ mul_comm _ _
      obtain rfl : s = e ⁻¹' t := by
        simp only [← ht, ← image_smul, smul_eq_mul, ← he, e.injective.preimage_image]
      simp only [← he, derivWithin, ← comp_def f e, e.comp_right_fderivWithin hsb, ← map_smul]
      simp [e]
    | inr hsb =>
      rw [derivWithin_zero_of_isolated hsb, derivWithin_zero_of_isolated, smul_zero]
      rw [← smul_eq_mul, ← Units.smul_def, ← Units.smul_def, ← smul_set_singleton,
        ← smul_set_sdiff, nhdsWithin_smul, hsb, smul_filter_bot]

theorem deriv_comp_mul_left {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) :
    deriv (f <| a * ·) b = a • deriv f (a * b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← derivWithin_univ, derivWithin_comp_mul_left, smul_set_univ₀ ha, derivWithin_univ]

theorem derivWithin_comp_neg {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (s : Set 𝕜) (a : 𝕜) :
    derivWithin (f <| -·) s a = -derivWithin f (-s) (-a) := by
  simpa using derivWithin_comp_mul_left f s (-1) a

-- theorem deriv_comp_

-- TODO: add `derivWithin_comp_add_left` etc
theorem derivWithin_comp_sub_left {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (s : Set 𝕜) (a b : 𝕜) :
    derivWithin (f <| a - ·) s b = -derivWithin f (a +ᵥ (-s)) (a - b) := by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·), derivWithin, derivWithin, fderivWithin_comp_add_left]

section PathIntegral


attribute [fun_prop] Continuous.IccExtend

theorem ContinuousMap.Homotopy.pathIntegral_add_pathIntegral_eq_of_hasFDerivWithinAt_of_contDiffOn
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path c d} {s : Set E}
    (φ : γ₁.toContinuousMap.Homotopy γ₂) (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ x ∈ s, ∀ a ∈ tangentConeAt ℝ s x, ∀ b ∈ tangentConeAt ℝ s x, dω x a b = dω x b a)
    (hφs : ∀ a, φ a ∈ s)
    (hF : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (I ×ˢ I)) :
    pathIntegral ω γ₁ + pathIntegral ω (φ.evalAt 1) =
      pathIntegral ω γ₂ + pathIntegral ω (φ.evalAt 0) := by
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2
  have hψs : ∀ a, ψ a ∈ s := fun _ ↦ hφs _
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hUI' : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq, Icc_prod_Icc]
    rfl
  have hUI : U ⊆ Icc 0 1 := hUI' ▸ interior_subset
  have hId : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E := fderivWithin ℝ dψ (Icc 0 1)
  rw [Icc_prod_Icc] at hF
  have hψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := fun a ha ↦
    hF.differentiableOn (by decide) a (hUI ha) |>.hasFDerivWithinAt
      |>.hasFDerivAt <| mem_of_superset (hUo.mem_nhds ha) hUI
  have hψc : Continuous ψ := by simp only [ψ]; fun_prop
  have hdψ : DifferentiableOn ℝ dψ (Icc 0 1) :=
    (hF.fderivWithin hId le_rfl).differentiableOn le_rfl
  have hdψIoo : ∀ a ∈ Ioo 0 1 ×ˢ Ioo 0 1, HasFDerivAt dψ (d2ψ a) a := fun a ha ↦ by
    refine hdψ _ (hUI ha) |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    exact mem_of_superset (hUo.mem_nhds ha) hUI
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hηc : ContinuousOn η (Icc 0 1) := by
    refine .clm_comp (.comp (t := s) ?_ ?_ ?_) ?_
    · exact fun x hx ↦ (hω x hx).continuousWithinAt
    · exact hψc.continuousOn
    · exact fun _ _ ↦ hψs _
    · exact hdψ.continuousOn
  have hη : ∀ a ∈ U, HasFDerivAt η (dη a) a := by
    rintro a ha
    have := (hω (ψ a) (hψs _)).comp_hasFDerivAt a (hψ a ha) (.of_forall fun _ ↦ hψs _)
    exact this.clm_comp (hdψIoo a ha)
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha x y
    simp only [d2ψ, dψ]
    apply Convex.second_derivative_within_at_symmetric (convex_Icc 0 1)
    · simp [hUI', U]
    · simpa only [hUI']
    · exact ha
    · exact (hdψ _ ha).hasFDerivWithinAt.mono interior_subset
  have hdη_symm : ∀ a ∈ Icc 0 1, ∀ x y, dη a x y = dη a y x := by
    intro a ha
    set S := Submodule.span ℝ (tangentConeAt ℝ s (ψ a))
    have H₁ : ∀ x ∈ S, ∀ y ∈ S, dω (ψ a) x y = dω (ψ a) y x := by
      intro x hx y hy
      induction hx, hy using Submodule.span_induction₂ with
      | mem_mem x y hx hy => exact hdω (ψ a) (hψs a) _ hx _ hy
      | zero_left => simp
      | zero_right => simp
      | add_left => simp [*]
      | add_right => simp [*]
      | smul_left => simp [*]
      | smul_right => simp [*]
    have H₂ (z): dψ a z ∈ S := by
      have := (hF.differentiableOn (by decide) a ha).hasFDerivWithinAt.mapsTo_tangent_cone
      refine (this.mono_right ?_).submoduleSpan ?_
      · exact tangentConeAt_mono (image_subset_iff.2 fun _ _ ↦ hψs _)
      · rw [(convex_Icc _ _).span_tangentConeAt] <;> simp [hUI', U, ha.1, ha.2]
    intro x y
    simp [dη, H₁ _ (H₂ x) _ (H₂ y), hd2ψ_symm a ha x y]
  have hdiv : EqOn (fun a : ℝ × ℝ ↦ f' a (1, 0) + g' a (0, 1)) 0 (Icc 0 1) := by
    intro a ha
    simp [f', g', hdη_symm a ha (1, 0)]
  have := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g f' g' 0 1 zero_le_one
    (hηc.clm_apply continuousOn_const) (hηc.clm_apply continuousOn_const).neg
    (fun a ha ↦ by exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hη a ha))
    (fun a ha ↦ by exact ((ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hη a ha)).neg)
    ?_
  · rw [setIntegral_congr_fun measurableSet_Icc hdiv, integral_zero'] at this
    have hφ₀ : φ.extend 0 = γ₁ := by
      ext
      apply φ.extend_apply_of_le_zero le_rfl
    have hfi (s : ℝ) (hs : s ∈ I) :
        ∫ t in (0)..1, f (s, t) = pathIntegral ω ⟨φ.extend s, rfl, rfl⟩ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [ContinuousLinearMap.comp_apply, pathIntegralFun, f, η, dψ]
      congr 1
      have : HasDerivWithinAt (fun u : ℝ ↦ ((s : ℝ), u)) (0, 1) I t :=
        (hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id _ _)
      rw [← this.derivWithin (uniqueDiffOn_Icc_zero_one _ ht), ← fderivWithin_comp_derivWithin]
      · rfl
      · refine hF.differentiableOn (by decide) _ ?_
        rw [← Icc_prod_Icc]
        exact ⟨hs, ht⟩
      · exact this.differentiableWithinAt
      · intro u hu
        rw [← Icc_prod_Icc]
        exact ⟨hs, hu⟩
    have hf₀ : ∫ t in (0)..1, f (0, t) = pathIntegral ω γ₁ := by
      rw [hfi 0 (by simp)]
      simp [pathIntegral, pathIntegralFun, Path.extend]
    have hf₁ : ∫ t in (0)..1, f (1, t) = pathIntegral ω γ₂ := by
      rw [hfi 1 (by simp)]
      simp [pathIntegral, pathIntegralFun, Path.extend]
    have hgt (s : I) : pathIntegral ω (φ.evalAt s) = -∫ t in (0)..1, g (t, s) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [ContinuousLinearMap.comp_apply, pathIntegralFun, g, η, dψ, neg_neg]
      congr 1
      · simp [ψ]
      · have : HasDerivWithinAt (fun u : ℝ ↦ (u, (s : ℝ))) (1, 0) I t :=
          (hasDerivWithinAt_id _ _).prodMk (hasDerivWithinAt_const _ _ _)
        rw [← this.derivWithin (uniqueDiffOn_Icc_zero_one _ ht),
          ← fderivWithin_comp_derivWithin (f := (·, s.1))]
        · simp [comp_def, ψ]
        · refine hF.differentiableOn (by decide) _ ?_
          rw [← Icc_prod_Icc]
          exact ⟨ht, s.2⟩
        · exact this.differentiableWithinAt
        · intro u hu
          rw [← Icc_prod_Icc]
          exact ⟨hu, s.2⟩
    rw [← hf₀, ← hf₁, hgt, hgt]
    linear_combination (norm := {dsimp; abel}) this
  · rw [integrableOn_congr_fun hdiv measurableSet_Icc]
    exact integrableOn_zero

@[simps]
def Path.segment (a b : E) : Path a b where
  toFun t := AffineMap.lineMap a b t.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  source' := by simp
  target' := by simp
  
@[simp]
lemma Path.segment_same (a : E) : Path.segment a a = .refl a := by
  ext t
  simp

@[simp]
lemma Path.cast_segment (h₁ : c = a) (h₂ : d = b) :
    (Path.segment a b).cast h₁ h₂ = .segment c d := by
  ext
  simp [h₁, h₂]

theorem pathIntegralFun_segment (ω : E → E →L[ℝ] F) (a b : E) {t : ℝ} (ht : t ∈ I) :
    pathIntegralFun ω (.segment a b) t = ω (lineMap a b t) (b - a) := by
  unfold pathIntegralFun
  have : EqOn (Path.segment a b).extend (lineMap a b) I := by
    intro t ht
    simp [*]
  rw [this ht, derivWithin_congr this (this ht)]
  congr 1
  -- TODO: `derivWithin` etc of `lineMap`
  simp only [AffineMap.coe_lineMap, vsub_eq_sub, vadd_eq_add]
  rw [derivWithin_add_const, derivWithin_smul_const, derivWithin_id', one_smul]
  exacts [uniqueDiffOn_Icc_zero_one t ht, differentiableWithinAt_id]

theorem pathIntegral_segment (ω : E → E →L[ℝ] F) (a b : E) :
    pathIntegral ω (.segment a b) = ∫ t in (0)..1, ω (lineMap a b t) (b - a) := by
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact pathIntegralFun_segment ω a b ht

theorem hasFDerivWithinAt_pathIntegral_segment_target_source {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F]
    {ω : E → E →L[𝕜] F} {s : Set E} (hs : Convex ℝ s) (hω : ContinuousOn ω s) (ha : a ∈ s) :
    HasFDerivWithinAt (pathIntegral (ω · |>.restrictScalars ℝ) <| .segment a ·) (ω a) s a := by
  simp only [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, Path.segment_same,
    pathIntegral_refl, sub_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  rcases Metric.continuousWithinAt_iff.mp (hω a ha) ε hε with ⟨δ, hδ₀, hδ⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have : ∫ t in (0)..1, ω a (b - a) = ω a (b - a) := by simp
  rw [pathIntegral_segment, ← this, ← intervalIntegral.integral_sub]
  · suffices ∀ t ∈ Ι (0 : ℝ) 1, ‖ω (lineMap a b t) (b - a) - ω a (b - a)‖ ≤ ε * ‖b - a‖ by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const this).trans_eq ?_
      simp
    intro t ht
    replace ht : t ∈ I := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    rw [← ContinuousLinearMap.sub_apply]
    apply ContinuousLinearMap.le_of_opNorm_le
    refine (hδ (hs.lineMap_mem ha hbs ht) ?_).le
    rw [dist_lineMap_left, Real.norm_of_nonneg ht.1]
    refine lt_of_le_of_lt ?_ hb
    rw [dist_comm]
    exact mul_le_of_le_one_left dist_nonneg ht.2
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    apply (ContinuousLinearMap.continuous_restrictScalars _).comp_continuousOn
    refine hω.comp ?_ ?_
    · simp only [AffineMap.coe_lineMap]
      fun_prop
    · exact fun _ ↦ hs.lineMap_mem ha hbs
  · simp

@[simps]
def ContinuousMap.Homotopy.linear {X : Type*} [TopologicalSpace X] (f g : C(X, E)) :
    f.Homotopy g where
  toFun x := Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]
lemma ContinuousMap.Homotopy.evalAt_linear {X : Type*} [TopologicalSpace X] (f g : C(X, E))
    (x : X) : (Homotopy.linear f g).evalAt x = .segment (f x) (g x) := rfl

theorem Convex.pathIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    pathIntegral ω (.segment a b) + pathIntegral ω (.segment b c) =
      pathIntegral ω (.segment a c) := by
  set φ := ContinuousMap.Homotopy.linear (Path.segment a b : C(I, E)) (Path.segment a c)
  have := φ.pathIntegral_add_pathIntegral_eq_of_hasFDerivWithinAt_of_contDiffOn hω hdω ?_ ?_
  · convert this using 2
    · simp only [φ]
      -- TODO: why do we need to explicitly give `f`?
      rw [ContinuousMap.Homotopy.evalAt_linear (Path.segment a b : C(I, E))]
      dsimp only [ContinuousMap.coe_coe]
      rw [← Path.cast_segment (Path.segment a b).target (Path.segment a c).target,
        pathIntegral_cast]
    · simp only [φ]
      rw [ContinuousMap.Homotopy.evalAt_linear (Path.segment a b : C(I, E))]
      dsimp only [ContinuousMap.coe_coe]
      rw [← Path.cast_segment (Path.segment a b).source (Path.segment a c).source]
      simp
  · aesop (add unsafe Convex.lineMap_mem)
  · have : EqOn (fun x : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend x.1) x.2)
        (fun x ↦ lineMap (lineMap a b x.2) (lineMap a c x.2) x.1) (I ×ˢ I) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift y to I using hy
      simp [φ, hx]
    refine .congr (ContDiff.contDiffOn ?_) this
    simp only [AffineMap.lineMap_apply_module]
    apply_rules [ContDiff.add, ContDiff.smul, contDiff_const, ContDiff.neg, contDiff_fst,
      contDiff_snd]

theorem Convex.hasFDerivWithinAt_pathIntegral_segment_of_hasFDerivWithinAt_symmetric
    [CompleteSpace F] {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) :
    HasFDerivWithinAt (fun x ↦ pathIntegral ω (.segment a x)) (ω b) s b := by
  suffices HasFDerivWithinAt (fun x ↦ pathIntegral ω (.segment a b) + pathIntegral ω (.segment b x))
      (ω b) s b from
    this.congr' (fun _ h ↦
      (hs.pathIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
  exact .const_add _ <| hasFDerivWithinAt_pathIntegral_segment_target_source hs
    (fun x hx ↦ (hω x hx).continuousWithinAt) hb

theorem Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (pathIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_pathIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

theorem Convex.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a,
      fderivWithin ℝ ω s a x y = fderivWithin ℝ ω s a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a :=
  hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha ↦ (hω a ha).hasFDerivWithinAt) hdω

theorem Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s) {ω : E → E →L[ℝ] F}
    (hω : DifferentiableOn ℝ ω s) (hdω : ∀ a ∈ s, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivAt f (ω a) a := by
  obtain ⟨f, hf⟩ : ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ ↦ ?_
    rw [fderivWithin_eq_fderiv, hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)]
  exact ⟨f, fun a ha ↦ (hf a ha).hasFDerivAt (hso.mem_nhds ha)⟩

end PathIntegral
