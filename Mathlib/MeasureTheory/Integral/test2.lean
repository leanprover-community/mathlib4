import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.OrthoDecomp
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section

open MeasureTheory Set Classical Filter Function Topology

variable {A E : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

#check Integrable.intervalIntegrable
#check intervalIntegral_tendsto_integral
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NormedRing 𝕜]

theorem MeasureTheory.Integrable.mul_bdd' {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    Integrable (fun x => g x * f x) μ := by
  apply Integrable.mono' (hg.norm.smul c) (hg.1.mul hf)
  filter_upwards [hf_bound] with x hx
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  calc
  ‖g x * f x‖ ≤ ‖g x‖ * ‖f x‖ := norm_mul_le _ _
  _           ≤ ‖f x‖ * ‖g x‖ := by rw [mul_comm]
  _           ≤ c * ‖g x‖ := by gcongr

theorem foo {u u' : ℝ → A}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Integrable u' volume) (x : ℝ) :
    ‖u x‖ ≤ ‖u 0‖ + ∫ y : ℝ, ‖u' y‖ := by
  have : ∫ (y : ℝ) in (0)..x, u' y = u x - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hu x) hu'.intervalIntegrable
  rw [(add_eq_of_eq_sub' this).symm]
  apply (norm_add_le _ _).trans
  gcongr
  apply intervalIntegral.norm_integral_le_integral_norm_Ioc.trans
  apply MeasureTheory.set_integral_le_integral
  · rwa [MeasureTheory.integrable_norm_iff hu'.1]
  · apply Filter.eventually_of_forall
    intro
    positivity

theorem integral_mul_deriv_eq_deriv_mul {a1 a2 a3 a4 : A} {u v u' v' : ℝ → A}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hu' : Integrable u' volume) (hv' : Integrable v' volume)
    (hu_atTop : Tendsto u atTop (𝓝 a1)) (hu_atBot : Tendsto u atBot (𝓝 a2))
    (hv_atTop : Tendsto v atTop (𝓝 a3)) (hv_atBot : Tendsto v atBot (𝓝 a4)) :
    ∫ x : ℝ, u x * v' x = a1 * a3 - a2 * a4 - ∫ x : ℝ, u' x * v x := by
  have h1 : Tendsto (fun a ↦ ∫ x in -a..a, u x * v' x) atTop (𝓝 (∫ x : ℝ, u x * v' x)) := by
    apply intervalIntegral_tendsto_integral
    · apply hv'.bdd_mul' (c := ‖u 0‖ + ∫ x : ℝ, ‖u' x‖)
      · apply Continuous.aestronglyMeasurable
        rw [continuous_iff_continuousAt]
        intro x
        exact (hu x).continuousAt
      · apply Filter.eventually_of_forall
        exact foo hu hu'
    · simp only [← Filter.comap_neg_atTop, Filter.tendsto_comap_iff, neg_involutive,
        Involutive.comp_self, tendsto_id]
    · exact tendsto_id
  have h' : (fun a ↦ ∫ x in -a..a, u x * v' x) =ᶠ[atTop]
      (fun a ↦ u a * v a - u (-a) * v (-a) - ∫ x in -a..a, u' x * v x) := by
    apply eventuallyEq_of_mem (Ioi_mem_atTop 0)
    intro x _
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
    · exact fun y _ ↦ hu y
    · exact fun y _ ↦ hv y
    · exact hu'.intervalIntegrable
    · exact hv'.intervalIntegrable
  have h2 : Tendsto (fun a ↦ ∫ x in -a..a, u x * v' x) atTop (𝓝 (a1 * a3 - a2 * a4 - ∫ x : ℝ, u' x * v x)) := by
    rw [Filter.tendsto_congr' h']
    apply Tendsto.sub
    · apply (hu_atTop.mul hv_atTop).sub
      simp only [← Filter.map_neg_atBot, Filter.tendsto_map'_iff]
      convert hu_atBot.mul hv_atBot
      simp only [comp_apply, neg_neg]
    apply intervalIntegral_tendsto_integral
    · apply hu'.mul_bdd' (c := ‖v 0‖ + ∫ x : ℝ, ‖v' x‖)
      · apply Continuous.aestronglyMeasurable
        rw [continuous_iff_continuousAt]
        intro x
        exact (hv x).continuousAt
      · apply Filter.eventually_of_forall
        exact foo hv hv'
    · simp only [← Filter.comap_neg_atTop, Filter.tendsto_comap_iff, neg_involutive,
        Involutive.comp_self, tendsto_id]
    · exact tendsto_id
  refine tendsto_nhds_unique' atTop_neBot h1 h2

open ZeroAtInfty

theorem integral_mul_deriv_eq_deriv_mul' {u v : C₀(ℝ, A)} {u' v' : ℝ → A}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hu' : Integrable u') (hv' : Integrable v') :
    ∫ x : ℝ, u x * v' x = - ∫ x : ℝ, u' x * v x := by
  have hu_atTop : Tendsto u atTop (𝓝 0) := (map_mono Real.atTop_le_cocompact).trans u.zero_at_infty'
  have hv_atTop : Tendsto v atTop (𝓝 0) := (map_mono Real.atTop_le_cocompact).trans v.zero_at_infty'
  have hu_atBot : Tendsto u atBot (𝓝 0) := (map_mono Real.atBot_le_cocompact).trans u.zero_at_infty'
  have hv_atBot : Tendsto v atBot (𝓝 0) := (map_mono Real.atBot_le_cocompact).trans v.zero_at_infty'
  have := integral_mul_deriv_eq_deriv_mul hu hv hu' hv' hu_atTop hu_atBot hv_atTop hv_atBot
  simp only [mul_zero, sub_self, zero_sub] at this
  exact this

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def coordinates (v : E) : E ≃ᵐ (Submodule.span ℝ {v} × (Submodule.span ℝ {v})ᗮ) where
  toEquiv := (InnerProductSpace.foo' (Submodule.span ℝ {v})).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (_ × _))
  measurable_toFun := by
    apply Continuous.measurable
    exact
      (WithLp.prod_continuous_equiv 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ)).comp
      (InnerProductSpace.foo' (Submodule.span ℝ {v})).continuous
  measurable_invFun := by
    apply Continuous.measurable
    exact
      (InnerProductSpace.foo' (Submodule.span ℝ {v})).symm.continuous.comp
      (WithLp.prod_continuous_equiv_symm 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ))

theorem coordinates_symm_apply (v : E) (a : Submodule.span ℝ {v}) (b : (Submodule.span ℝ {v})ᗮ) :
    (coordinates v).symm (a, b) = a + b := by
  unfold coordinates
  simp only [MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk]
  rw [Equiv.symm_apply_eq]
  ext
  · simp [InnerProductSpace.foo'_apply', InnerProductSpace.foo'_apply]
    rw [Prod.fst_add]
    simp
  · simp [InnerProductSpace.foo'_apply', InnerProductSpace.foo'_apply]
    rw [Prod.snd_add]
    simp

#check LinearEquiv.toSpanNonzeroSingleton

@[simp] theorem toSpanNonzeroSingleton_apply (v : E) (h : v ≠ 0) (t : ℝ) :
    LinearEquiv.toSpanNonzeroSingleton ℝ E v h t =
      (⟨t • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩ :
      Submodule.span ℝ {v}) := by
  rfl

def toSpanUnitSingleton (v : E) (hv : ‖v‖ = 1) : ℝ ≃ₗᵢ[ℝ] Submodule.span ℝ {v} where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton ℝ E v (by
    rw [← norm_ne_zero_iff, hv]
    simp only [ne_eq, one_ne_zero, not_false_eq_true])
  norm_map' := by
    intro x
    simp [toSpanNonzeroSingleton_apply, norm_smul, hv]

@[simp] theorem toSpanUnitSingleton_apply (v : E) (hv : ‖v‖ = 1) (t : ℝ) :
    toSpanUnitSingleton v hv t =
      (⟨t • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩ :
      Submodule.span ℝ {v}) := by
  rfl

theorem coordinates_measurePreserving (v : E) : MeasurePreserving (coordinates v) := by
  convert MeasureTheory.MeasurePreserving.comp
    (WithLp.equiv_prod_measurePreserving (Submodule.span ℝ {v}) (Submodule.span ℝ {v})ᗮ)
    ((InnerProductSpace.foo' (Submodule.span ℝ {v})).measurePreserving)

/-
def coordinates (v : E) : E ≃ₗ[ℝ] (Submodule.span ℝ {v} × (Submodule.span ℝ {v})ᗮ) :=
  (InnerProductSpace.foo' (Submodule.span ℝ {v})).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (_ × _))

def coordinates_m (v : E) : E ≃ᵐ (Submodule.span ℝ {v} × (Submodule.span ℝ {v})ᗮ) where
  toEquiv := (InnerProductSpace.foo' (Submodule.span ℝ {v})).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (_ × _))
  measurable_toFun := by
    apply Continuous.measurable
    exact
      (WithLp.prod_continuous_equiv 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ)).comp
      (InnerProductSpace.foo' (Submodule.span ℝ {v})).continuous
  measurable_invFun := by
    apply Continuous.measurable
    exact
      (InnerProductSpace.foo' (Submodule.span ℝ {v})).symm.continuous.comp
      (WithLp.prod_continuous_equiv_symm 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ))

theorem coordinates_measurePreserving (v : E) : MeasurePreserving (coordinates v) := by
  convert MeasureTheory.MeasurePreserving.comp
    (WithLp.equiv_prod_measurePreserving (Submodule.span ℝ {v}) (Submodule.span ℝ {v})ᗮ)
    (InnerProductSpace.foo2 (InnerProductSpace.foo' (Submodule.span ℝ {v})))

def coordinates' (v : E) : (Submodule.span ℝ {v} × (Submodule.span ℝ {v})ᗮ) ≃ₗ[ℝ] E :=
  ((InnerProductSpace.foo' (Submodule.span ℝ {v})).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (_ × _))).symm

theorem coordinates'_measurePreserving (v : E) : MeasurePreserving (coordinates' v) := by
  have : MeasurePreserving (coordinates_m v) := by
    convert coordinates_measurePreserving v
  convert this.symm
-/


theorem foo1235 (v : E) (u u' : E → A) (hu : ∀ x, HasLineDerivAt ℝ u (u' x) x v) (y : E) (t : ℝ) :
    HasDerivAt (fun x ↦ u (x • v + y)) (u' (t • v + y)) t := by
  specialize hu (t • v + y)
  unfold HasLineDerivAt at hu
  rw [← add_neg_self t] at hu
  have := hu.comp_add_const t (-t)
  convert this using 3
  simp_rw [add_comm _ y, add_assoc, ← add_smul]
  ring_nf

theorem integration_by_parts (v : E) (hv : ‖v‖ = 1) (u1 u2 : C₀(E, A)) {u1' u2' : E → A}
    (hu1 : ∀ x, HasLineDerivAt ℝ u1 (u1' x) x v) (hu2 : ∀ x, HasLineDerivAt ℝ u2 (u2' x) x v)
    (hu1' : Integrable u1') (hu2' : Integrable u2') :
    ∫ x : E, u1 x * u2' x = - ∫ x : E, u1' x * u2 x := by
  simp_rw [← ((coordinates_measurePreserving v).symm _).integral_comp',
    MeasureTheory.Measure.volume_eq_prod]
  have hint1_left : Integrable fun x ↦ u1' ((coordinates v).symm x) := by
    erw [MeasurePreserving.integrable_comp_emb]
    · exact hu1'
    · exact (coordinates_measurePreserving v).symm
    exact (coordinates v).symm.measurableEmbedding
  have hint2_right : Integrable fun x ↦ u2' ((coordinates v).symm x) := by
    sorry
  have hint1 : Integrable fun x ↦ u1' ((coordinates v).symm x) * u2 ((coordinates v).symm x) := by
    have h2 : AEStronglyMeasurable (u2 ∘ (coordinates v).symm) volume := by
      apply Continuous.aestronglyMeasurable
      apply u2.continuous.comp
      exact (InnerProductSpace.foo' (Submodule.span ℝ {v})).symm.continuous.comp
        (WithLp.prod_continuous_equiv_symm 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ))
    apply hint1_left.mul_bdd' (c := ‖u2‖) h2
    apply Filter.eventually_of_forall
    intro y
    simp only [comp_apply]
    have := u2.toBCF.norm_coe_le_norm ((coordinates v).symm y)
    simp only [ZeroAtInftyContinuousMap.toBCF_toFun,
      ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at this
    exact this
  have hint2 : Integrable fun x ↦ u1 ((coordinates v).symm x) * u2' ((coordinates v).symm x) := by
    sorry
  rw [MeasureTheory.integral_prod_symm _ hint1, MeasureTheory.integral_prod_symm _ hint2]
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  rcases hint1_left.prod_left_ae.exists_mem with ⟨s1, hs1, hs1'⟩
  rcases hint2_right.prod_left_ae.exists_mem with ⟨s2, hs2, hs2'⟩
  apply Filter.eventuallyEq_of_mem (Filter.inter_mem hs1 hs2)
  intro y hy
  specialize hs1' y (Set.mem_of_mem_inter_left hy)
  specialize hs2' y (Set.mem_of_mem_inter_right hy)
  simp only [coordinates_symm_apply, ← (toSpanUnitSingleton v hv).integral_comp,
    ← (toSpanUnitSingleton v hv).integrable_comp, toSpanUnitSingleton_apply] at hs1' hs2' ⊢
  let u1_ : ℝ → A := fun x ↦ u1 (x • v + y)
  let u2_ : ℝ → A := fun x ↦ u2 (x • v + y)
  let u1'_ : ℝ → A := fun x ↦ u1' (x • v + y)
  let u2'_ : ℝ → A := fun x ↦ u2' (x • v + y)
  have hu1_deriv : ∀ x, HasDerivAt u1_ (u1'_ x) x := foo1235 v u1 u1' hu1 y
  have hu2_deriv : ∀ x, HasDerivAt u2_ (u2'_ x) x := foo1235 v u2 u2' hu2 y
  have hu1_atTop : Tendsto u1_ atTop (𝓝 0) := by
    have := u1.zero_at_infty'
    sorry
    --(map_mono Real.atTop_le_cocompact).trans u.zero_at_infty'
  have hu2_atTop : Tendsto u2_ atTop (𝓝 0) := by
    sorry
    --(map_mono Real.atTop_le_cocompact).trans v.zero_at_infty'
  have hu1_atBot : Tendsto u1_ atBot (𝓝 0) := by
    sorry
    --(map_mono Real.atBot_le_cocompact).trans u.zero_at_infty'
  have hu2_atBot : Tendsto u2_ atBot (𝓝 0) := by
    sorry
    --(map_mono Real.atBot_le_cocompact).trans v.zero_at_infty'
  change ∫ x, u1_ x * u2'_ x = - ∫ x, u1'_ x * u2_ x
  -- Show that all of these are in C₀
  have h := integral_mul_deriv_eq_deriv_mul hu1_deriv hu2_deriv hs1' hs2' hu1_atTop hu1_atBot
    hu2_atTop hu2_atBot
  simp only [mul_zero, sub_self, zero_sub] at h
  exact h
  /-· -- hint1
    let u1'_ := fun x ↦ u1' ((coordinates v).symm x)
    let u2_ := fun x ↦ u2 ((coordinates v).symm x)
    change Integrable (fun x ↦ u1'_ x * u2_ x)

    have h1 : Integrable u1'_ := by
      erw [MeasurePreserving.integrable_comp_emb]
      · exact hu1'
      · exact (coordinates_measurePreserving v).symm
      exact (coordinates v).symm.measurableEmbedding
    have h2 : AEStronglyMeasurable (u2 ∘ (coordinates v).symm) volume := by
      apply Continuous.aestronglyMeasurable
      apply u2.continuous.comp
      exact (InnerProductSpace.foo' (Submodule.span ℝ {v})).symm.continuous.comp
        (WithLp.prod_continuous_equiv_symm 2 (Submodule.span ℝ {v}) ((Submodule.span ℝ {v})ᗮ))
    apply h1.mul_bdd' (c := ‖u2‖) h2
    apply Filter.eventually_of_forall
    intro y
    simp only [comp_apply]
    -- Trivial after refactoring ZeroAtInftyContinuousMap
    sorry
  · -- Same as previous case
    sorry-/
