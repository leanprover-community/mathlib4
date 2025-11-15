/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne, Kexing Ying
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.Holder

/-!
# Pull-out property of the conditional expectation

Let `Ω` be endowed with a measurable space structure `mΩ`, and let `m : MeasurableSpace Ω` such that
`m ≤ mΩ`. Let `μ` be a measure over `Ω`. Let `B : F →L[ℝ] E →L[ℝ] G` a continuous bilinear map,
`f : Ω → F` and `g : Ω → E` such that `fun ω ↦ B (f ω) (g ω)` is integrable, `g` is integrable
and `f` is `AEStronglyMeasurable` with respect to `m`. The **pull-out** property of the conditional
expectation states that almost surely, `μ[B f g|m] = B f μ[g|m]`.

We specialize this statement to the cases where `B` is scalar multiplication and multiplication.

# Main statements

* `condExp_bilin_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[B f g|m] = B f μ[g|m]`.
* `condExp_smul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f • g|m] = f • μ[g|m]`.
* `condExp_mul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f * g|m] = f * μ[g|m]`.

# Tags

conditional expectation, pull-out, bilinear map
-/

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] (B : F →L[ℝ] E →L[ℝ] G)

/-- Auxiliary lemma for `condExp_bilin_of_stronglyMeasurable_left`. -/
theorem condExp_stronglyMeasurable_simpleFunc_bilin [CompleteSpace E]
    (hm : m ≤ mΩ) (f : @SimpleFunc Ω m F) {g : Ω → E} (hg : Integrable g μ) :
    μ[fun a ↦ B (f a) (g a)|m] =ᵐ[μ] fun a ↦ B (f a) (μ[g|m] a) := by
  have : ∀ (s c) (f : Ω → E),
      (fun x ↦ B (Set.indicator s (Function.const Ω c) x) (f x)) =
        s.indicator (fun a ↦ B c (f a)) := by
    intro s c f
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this, this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with x hx
    simp only [Function.comp_apply] at hx
    classical simp_rw [Set.indicator_apply, hx]
    rfl
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun a ↦ B (g₁ a + g₂ a) (g a)|m] =ᵐ[μ]
          μ[fun a ↦ B (g₁ a) (g a)|m] + μ[fun a ↦ B (g₂ a) (g a)|m] := by
        simp_rw [B.map_add]
        exact condExp_add (hg.simpleFunc_bilinearMap' B hm g₁)
          (hg.simpleFunc_bilinearMap' B hm g₂) m
      _ =ᵐ[μ] fun a ↦ B (g₁ a) (μ[g|m] a) + B (g₂ a) (μ[g|m] a) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun a ↦ B ((g₁ + g₂) a) (μ[g|m] a) := by simp

theorem condExp_stronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → F} {g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    μ[fun a ↦ B (f a) (g a)|m] =ᵐ[μ] fun a ↦ B (f a) (μ[g|m] a) := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ x ∂μ, Tendsto (fs · x) atTop (𝓝 (f x)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hf_bound.exists with ⟨_x, hx⟩
    exact (norm_nonneg _).trans hx
  have hfs_bound : ∀ n x, ‖fs n x‖ ≤ c := hf.norm_approxBounded_le hc
  have : μ[fun a ↦ B (f a) (μ[g|m] a)|m] = fun a ↦ B (f a) (μ[g|m] a) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n x => B (fs n x) (g x))
    (fun n x => B (fs n x) (μ[g|m] x)) (fun x ↦ B (f x) (g x))
    (fun x ↦ B (f x) (μ[g|m] x)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g|m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with x hx
    exact ((by fun_prop : Continuous (fun y ↦ B y (g x))).tendsto (f x)).comp hx
  · filter_upwards [hfs_tendsto] with x hx
    exact ((by fun_prop : Continuous (fun y ↦ B y (μ[g|m] x))).tendsto (f x)).comp hx
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n => Eventually.of_forall fun x => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n => Eventually.of_forall fun x => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_stronglyMeasurable_left [CompleteSpace E] {f : Ω → F} {g : Ω → E}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hg : Integrable g μ) :
    μ[fun x ↦ B (f x) (g x)|m] =ᵐ[μ] fun x ↦ B (f x) (μ[g|m] x) := by
  by_cases hm : m ≤ mΩ; swap; · exact ae_of_all _ <| by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · exact ae_of_all _ <| by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices ∀ n, ∀ᵐ x ∂μ, x ∈ sets n → (μ[fun x ↦ B (f x) (g x)|m]) x = B (f x) (μ[g|m] x) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx
    obtain ⟨i, hi⟩ : ∃ i, x ∈ sets i := by
      have h_mem : x ∈ ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hx i hi
  refine fun n => ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun x ↦ B (f x) (g x)|m] =ᵐ[μ.restrict (sets n)]
      fun x ↦ B (f x) ((μ.restrict (sets n))[g|m] x) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with x hx1 hx2
    rw [hx1, hx2]
  suffices (μ.restrict (sets n))[fun x ↦ B ((sets n).indicator f x) (g x)|m] =ᵐ[μ.restrict (sets n)]
      fun x ↦ B ((sets n).indicator f x) ((μ.restrict (sets n))[g|m] x) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with x hx
      rw [hx]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with x hx
      rw [hx]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with x
  by_cases hxs : x ∈ sets n <;> simp [hxs, h_norm]

/-- Pull-out property of the conditional expectation. -/
lemma condExp_bilin_of_stronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ) (hf : Integrable f μ) :
    μ[fun x ↦ B (f x) (g x) | m] =ᵐ[μ] fun x ↦ B (μ[f | m] x) (g x) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_bilin_of_aestronglyMeasurable_left [CompleteSpace E]
    {f : Ω → F} {g : Ω → E} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ) (hg : Integrable g μ) :
    μ[fun x ↦ B (f x) (g x)|m] =ᵐ[μ] fun x ↦ B (f x) (μ[g|m] x) := calc
  μ[fun x ↦ B (f x) (g x)|m]
  _ =ᵐ[μ] μ[fun x ↦ B (hf.mk f x) (g x)|m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun x ↦ B (hf.mk f x) (μ[g|m] x) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with x hx using by rw [hx]
  _ =ᵐ[μ] fun x ↦ B (f x) (μ[g|m] x) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]

/-- Pull-out property of the conditional expectation. -/
lemma condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ) (hf : Integrable f μ) :
    μ[fun x ↦ B (f x) (g x) | m] =ᵐ[μ] fun x ↦ B (μ[f | m] x) (g x) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_smul_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ) :
    μ[f • g|m] =ᵐ[μ] f • μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).flip hf hfg hg

/-- Pull-out property of the conditional expectation. -/
theorem condExp_smul_of_aestronglyMeasurable_right [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : Integrable f μ) (hfg : Integrable (f • g) μ) (hg : AEStronglyMeasurable[m] g μ) :
    μ[f • g|m] =ᵐ[μ] μ[f|m] • g :=
  condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)) hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_aestronglyMeasurable_left {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) hf hfg hg

/-- Pull-out property of the conditional expectation. -/
lemma condExp_mul_of_aestronglyMeasurable_right {f g : Ω → ℝ} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (ContinuousLinearMap.mul ℝ ℝ) hg hfg hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_stronglyMeasurable_left {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ)
    hf.aestronglyMeasurable hfg hg

/-- Pull-out property of the conditional expectation. -/
lemma condExp_mul_of_stronglyMeasurable_right {f g : Ω → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (ContinuousLinearMap.mul ℝ ℝ)
    hg.aestronglyMeasurable hfg hf

end MeasureTheory
