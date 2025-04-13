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

open scoped unitInterval Pointwise Topology
open Function Set MeasureTheory Filter

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

@[simp]
protected theorem HasFDerivWithinAt.empty {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {a : E} : HasFDerivWithinAt f f' ∅ a := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

theorem Set.Finite.hasFDerivWithinAt {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {a : E} (hs : s.Finite) :
    HasFDerivWithinAt f f' s a := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ hs ihs => exact ihs.insert'

theorem Set.Subsingleton.hasFDerivWithinAt {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {a : E} (hs : s.Subsingleton) :
    HasFDerivWithinAt f f' s a :=
  hs.finite.hasFDerivWithinAt

theorem Set.Finite.fderivWithin_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : s.Finite) (f : E → F) : fderivWithin 𝕜 f s = 0 := by
  ext1 x
  simp [fderivWithin, hs.hasFDerivWithinAt]

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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b c d : E}

noncomputable def pathIntegralFun (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) : F :=
  ω (γ.extend t) (derivWithin γ.extend I t)

noncomputable def pathIntegral (ω : E → E →L[ℝ] F) (γ : Path a b) : F :=
  ∫ t in (0)..1, pathIntegralFun ω γ t

def PathIntegrable (ω : E → E →L[ℝ] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (pathIntegralFun ω γ) volume 0 1

theorem pathIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E → E →L[ℝ] F)
    (γ : Path a b) : pathIntegral ω γ = 0 := by
  simp [pathIntegral, intervalIntegral, integral, h]

@[simp]
theorem pathIntegralFun_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegralFun ω (.refl a) = 0 := by
  ext
  simp [pathIntegralFun]

@[simp]
theorem pathIntegral_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegral ω (.refl a) = 0 := by
  simp [pathIntegral]

@[simp]
theorem PathIntegrable.refl (ω : E → E →L[ℝ] F) (a : E) : PathIntegrable ω (.refl a) := by
  simp [PathIntegrable, Pi.zero_def]

theorem pathIntegralFun_symm_apply (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) :
    pathIntegralFun ω γ.symm t = -pathIntegralFun ω γ (1 - t) := by
  simp [pathIntegralFun, γ.extend_symm, derivWithin_comp_sub_left]

@[simp]
theorem pathIntegralFun_symm (ω : E → E →L[ℝ] F) (γ : Path a b):
    pathIntegralFun ω γ.symm = (-pathIntegralFun ω γ <| 1 - ·) :=
  funext <| pathIntegralFun_symm_apply ω γ

protected theorem PathIntegrable.symm {ω : E → E →L[ℝ] F} {γ : Path a b} (h : PathIntegrable ω γ) :
    PathIntegrable ω γ.symm := by
  simpa [PathIntegrable] using (h.comp_sub_left 1).neg.symm

@[simp]
theorem pathIntegrable_symm {ω : E → E →L[ℝ] F} {γ : Path a b} :
    PathIntegrable ω γ.symm ↔ PathIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem pathIntegral_symm (ω : E → E →L[ℝ] F) (γ : Path a b) :
    pathIntegral ω γ.symm = -pathIntegral ω γ := by
  simp [pathIntegral, pathIntegralFun_symm]

theorem pathIntegralFun_trans_of_lt_half (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c)
    {t : ℝ} (ht₀ : 0 < t) (ht : t < 1 / 2) :
    pathIntegralFun ω (γ₁.trans γ₂) t = (2 : ℝ) • pathIntegralFun ω γ₁ (2 * t) := by
  have : (γ₁.trans γ₂).extend =ᶠ[𝓝 t] (fun s ↦ γ₁.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ ↦ Path.extend_trans_of_le_half _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left, map_smul] <;>
    apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeEq_left (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c) :
    pathIntegralFun ω (γ₁.trans γ₂) =ᵐ[volume.restrict (Ι (0 : ℝ) (1 / 2))]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γ₁ (2 * t) := by
  rw [uIoc_of_le (by positivity), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact pathIntegralFun_trans_of_lt_half ω γ₁ γ₂ ht₀ ht

theorem pathIntegralFun_trans_of_half_lt (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c)
    {t : ℝ} (ht₀ : 1 / 2 < t) (ht : t < 1) :
    pathIntegralFun ω (γ₁.trans γ₂) t = (2 : ℝ) • pathIntegralFun ω γ₂ (2 * t - 1) := by
  have : (γ₁.trans γ₂).extend =ᶠ[𝓝 t] (fun s ↦ γ₂.extend (2 * s - 1)) :=
    (eventually_ge_nhds ht₀).mono fun _ ↦ Path.extend_trans_of_half_le _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left (γ₂.extend <| · - 1), deriv_comp_sub_const,
    map_smul] <;> apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeEq_right (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c) :
    pathIntegralFun ω (γ₁.trans γ₂) =ᵐ[volume.restrict (Ι (1 / 2 : ℝ) 1)]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γ₂ (2 * t - 1) := by
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact pathIntegralFun_trans_of_half_lt ω γ₁ γ₂ ht₁ ht₂

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_left {ω : E → E →L[ℝ] F}
    {γ₁ : Path a b} (h : PathIntegrable ω γ₁) (γ₂ : Path b c) :
    IntervalIntegrable (pathIntegralFun ω (γ₁.trans γ₂)) volume 0 (1 / 2) :=
  .congr (by simpa using (h.comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeEq_left _ _ _).symm

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_right {ω : E → E →L[ℝ] F}
    (γ₁ : Path a b) {γ₂ : Path b c} (h : PathIntegrable ω γ₂) :
    IntervalIntegrable (pathIntegralFun ω (γ₁.trans γ₂)) volume (1 / 2) 1 :=
  .congr (by simpa using ((h.comp_sub_right 1).comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeEq_right _ _ _).symm

protected theorem PathIntegrable.trans {ω : E → E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : PathIntegrable ω γ₁) (h₂ : PathIntegrable ω γ₂) : PathIntegrable ω (γ₁.trans γ₂) :=
  (h₁.intervalIntegrable_pathIntegralFun_trans_left γ₂).trans
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γ₁)

theorem pathIntegral_trans {ω : E → E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : PathIntegrable ω γ₁) (h₂ : PathIntegrable ω γ₂) :
    pathIntegral ω (γ₁.trans γ₂) = pathIntegral ω γ₁ + pathIntegral ω γ₂ := by
  rw [pathIntegral, ← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_pathIntegralFun_trans_left γ₂)
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γ₁),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeEq_left _ _ _),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeEq_right _ _ _),
    intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
    intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_left (f := (pathIntegralFun ω γ₂ <| · - 1)),
    intervalIntegral.integral_comp_sub_right]
  norm_num [pathIntegral]

-- ω (γ.extend t) (derivWithin γ.extend I t)

/-- If a 1-form `ω` is continuous on a set `s`,
then it is path integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.pathIntegrable_of_contDiffOn {ω : E → E →L[ℝ] F} {γ : Path a b}
    {s : Set E} (hω : ContinuousOn ω s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    PathIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  unfold pathIntegralFun
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ ↦ hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

/-
theorem integral_divergence_prod_Icc_of_hasFDerivAt_of_le (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
-/

attribute [fun_prop] Continuous.IccExtend

theorem Path.Homotopy.pathIntegral_add_pathIntegral_eq_of_hasFDerivWithinAt_of_contDiffOn
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path c d} {s : Set E}
    (φ : γ₁.toContinuousMap.Homotopy γ₂) (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ x ∈ s, ∀ a b, dω x a b = dω x b a) (hφs : ∀ a, φ a ∈ s)
    (hF : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend xy.1) xy.2) (I ×ˢ I)) :
    pathIntegral ω γ₁ + pathIntegral ω (φ.evalAt 1) =
      pathIntegral ω γ₂ + pathIntegral ω (φ.evalAt 0) := by
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend xy.1) xy.2
  have hψs : ∀ a, ψ a ∈ s := fun _ ↦ hφs _
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hUI' : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq, Icc_prod_Icc]
    rfl
  have hUI : U ⊆ Icc 0 1 := hUI' ▸ interior_subset
  have hId : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hψ' : ContDiffOn ℝ 2 ψ U := hF.mono <| by
    simp only [U]
    gcongr <;> exact Ioo_subset_Icc_self
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
    intro a ha x y
    simp [dη, hdω (ψ a) (hψs a) (dψ a x), hd2ψ_symm a ha x y]
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
    have hfi (s : I) : ∫ t in (0)..1, f (s, t) = pathIntegral ω ⟨φ.extend s, rfl, rfl⟩ := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ ?_
      simp only [ContinuousLinearMap.comp_apply, pathIntegralFun, f, η, dψ]
      congr 1
      have : HasDerivWithinAt (fun u : ℝ ↦ ((s : ℝ), u)) (0, 1) I t :=
        (hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id _ _)
      rw [← this.derivWithin (uniqueDiffOn_Icc_zero_one _ <| Ioo_subset_Icc_self ht),
        ← fderivWithin_comp_derivWithin]
      · rfl
      · refine hF.differentiableOn (by decide) _ ?_
        rw [← Icc_prod_Icc]
        exact ⟨s.2, Ioo_subset_Icc_self ht⟩
      · exact this.differentiableWithinAt
    have hf₀ : ∫ t in (0)..1, f (0, t) = pathIntegral ω γ₁ := by
      rw [← unitInterval.coe_zero, hfi]
      
  · rw [integrableOn_congr_fun hdiv measurableSet_Icc]
    exact integrableOn_zero
    -- (fun a ha ↦ (ContinuousLinearMap.apply ℝ _ (1, 0)).hasFDerivAt.comp a (hη a ha))

end PathIntegral
