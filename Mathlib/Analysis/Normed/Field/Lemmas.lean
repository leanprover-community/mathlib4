/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Analysis.Normed.MulAction

/-!
# Normed fields

In this file we continue building the theory of normed division rings and fields.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `discreteTopology_or_nontriviallyNormedField`
* `discreteTopology_of_bddAbove_range_norm`

-/

@[expose] public section

-- Guard against import creep.
assert_not_exists RestrictScalars

variable {α β ι : Type*}

open Filter Bornology Metric
open scoped Topology NNReal Pointwise Uniformity

section NormedDivisionRing

variable [NormedDivisionRing α]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

namespace Filter

@[simp]
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
lemma inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[≠] 0 := by
  rw [← comap_norm_atTop, ← Filter.comap_inv, ← comap_norm_nhdsGT_zero, ← inv_atTop₀,
    ← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]
lemma inv_nhdsNE_zero : (𝓝[≠] (0 : α))⁻¹ = cobounded α := by
  rw [← inv_cobounded₀, inv_inv]

@[deprecated (since := "2025-11-26")] alias inv_nhdsWithin_ne_zero := inv_nhdsNE_zero

lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded α) (𝓝[≠] 0) :=
  inv_cobounded₀.le

theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left

lemma tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded α) :=
  inv_nhdsNE_zero.le

@[deprecated (since := "2025-11-26")]
alias tendsto_inv₀_nhdsWithin_ne_zero := tendsto_inv₀_nhdsNE_zero

end Filter

/-- If `s` is a set disjoint from `𝓝 0`, then `fun x ↦ x⁻¹` is uniformly continuous on `s`. -/
theorem uniformContinuousOn_inv₀ {s : Set α} (hs : sᶜ ∈ 𝓝 0) :
    UniformContinuousOn Inv.inv s := by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddCommGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := s), Set.compl_setOf, not_lt] at hr
  have hs₀ : ∀ x ∈ s, x ≠ 0 := fun x hx ↦ norm_pos_iff.mp <| hr₀.trans_le (hr hx)
  refine ⟨ε * r ^ 2, by positivity, fun x hx y hy hxy ↦ ?_⟩
  calc
    dist x⁻¹ y⁻¹ = ‖x‖⁻¹ * dist y x * ‖y‖⁻¹ := by
      simp [dist_eq_norm, inv_sub_inv' (hs₀ x hx) (hs₀ y hy)]
    _ ≤ r⁻¹ * (ε * r ^ 2) * r⁻¹ := by
      rw [dist_comm]
      gcongr <;> exact hr ‹_›
    _ = ε := by field_simp

@[to_fun]
theorem UniformContinuousOn.inv₀ {X : Type*} [UniformSpace X] {f : X → α} {s : Set X}
    (hf : UniformContinuousOn f s) (hf₀ : (f '' s)ᶜ ∈ 𝓝 0) :
    UniformContinuousOn f⁻¹ s :=
  uniformContinuousOn_inv₀ hf₀ |>.comp hf (Set.mapsTo_image f s)

@[to_fun]
theorem UniformContinuous.inv₀ {X : Type*} [UniformSpace X] {f : X → α}
    (hf : UniformContinuous f) (hf₀ : (Set.range f)ᶜ ∈ 𝓝 0) :
    UniformContinuous f⁻¹ := by
  simp only [← uniformContinuousOn_univ, ← Set.image_univ] at *
  exact hf.inv₀ hf₀

@[to_fun]
theorem TendstoLocallyUniformlyOn.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ∀ x ∈ s, Disjoint (map f (𝓝[s] x)) (𝓝 0)) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases basis_sets _ |>.map _ |>.disjoint_iff nhds_basis_ball
    |>.mp (hf x hx) with ⟨U, hUx, r, hr₀, hr⟩
  refine Tendsto.comp (uniformContinuousOn_inv₀ (s := (closedBall (0 : α) (r / 2))ᶜ)
    (by simp [closedBall_mem_nhds, hr₀])) <| tendsto_inf.mpr ⟨hF x hx, tendsto_principal.mpr ?_⟩
  filter_upwards [hF x hx (dist_mem_uniformity (half_pos hr₀)), tendsto_snd hUx] with y hy₁ hy₂
  have : r ≤ ‖f y.2‖ := by simp_all [Set.disjoint_left]
  have : r / 2 < ‖F y.1 y.2‖ := by
    simp [dist_eq_norm_sub] at hy₁
    linarith [hy₁, norm_sub_norm_le (f y.2) (F y.1 y.2)]
  simp_all [(half_lt_self hr₀).trans_le]

@[to_fun]
theorem TendstoLocallyUniformly.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : ∀ x, Disjoint (map f (𝓝 x)) (𝓝 0)) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.inv₀_of_disjoint
  simpa

@[to_fun]
theorem TendstoLocallyUniformlyOn.inv₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ContinuousOn f s) (hf₀ : ∀ x ∈ s, f x ≠ 0) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s :=
  hF.inv₀_of_disjoint fun x hx ↦ disjoint_nhds_nhds.2 (hf₀ x hx) |>.mono_left (hf x hx)

@[to_fun]
theorem TendstoLocallyUniformly.inv₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : Continuous f) (hf₀ : ∀ x, f x ≠ 0) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l :=
  hF.inv₀_of_disjoint fun x ↦ disjoint_nhds_nhds.2 (hf₀ x) |>.mono_left (hf.tendsto x)

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_continuousInv₀ : ContinuousInv₀ α where
  continuousAt_inv₀ x hx := by
    refine uniformContinuousOn_inv₀ (s := (Metric.closedBall x (‖x‖ / 2))) ?_
      |>.continuousOn |>.continuousAt ?_
    · refine Metric.isClosed_closedBall.isOpen_compl.mem_nhds ?_
      simpa
    · apply Metric.closedBall_mem_nhds
      simpa

@[deprecated (since := "2025-09-01")] alias NormedDivisionRing.to_hasContinuousInv₀ :=
  NormedDivisionRing.to_continuousInv₀

@[to_fun]
theorem TendstoLocallyUniformlyOn.div₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hg₀ : ∀ x ∈ s, g x ≠ 0) :
    TendstoLocallyUniformlyOn (F / G) (f / g) l s := by
  simp only [div_eq_mul_inv]
  exact hF.mul₀ (hG.inv₀ hg hg₀) hf <| hg.inv₀ hg₀

@[to_fun]
theorem TendstoLocallyUniformly.div₀ {X ι : Type*} [TopologicalSpace X]
    {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) (hg₀ : ∀ x, g x ≠ 0) :
    TendstoLocallyUniformly (F / G) (f / g) l := by
  simp only [div_eq_mul_inv]
  exact hF.mul₀ (hG.inv₀ hg hg₀) hf <| hg.inv₀ hg₀

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_isTopologicalDivisionRing :
    IsTopologicalDivisionRing α where

lemma tendsto_norm_inv_nhdsNE_zero_atTop : Tendsto (fun x : α ↦ ‖x⁻¹‖) (𝓝[≠] 0) atTop :=
  tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero

@[deprecated (since := "2025-11-26")]
alias NormedField.tendsto_norm_inv_nhdsNE_zero_atTop := tendsto_norm_inv_nhdsNE_zero_atTop

lemma tendsto_zpow_nhdsNE_zero_cobounded {m : ℤ} (hm : m < 0) :
    Tendsto (· ^ m) (𝓝[≠] 0) (cobounded α) := by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to ℕ using by lia
  simpa [Function.comp_def] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

@[deprecated tendsto_zpow_nhdsNE_zero_cobounded (since := "2025-11-26")]
lemma NormedField.tendsto_norm_zpow_nhdsNE_zero_atTop {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : α ↦ ‖x ^ m‖) (𝓝[≠] 0) atTop :=
  tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded hm)

end NormedDivisionRing

namespace NormedField

/-- A normed field is either nontrivially normed or has a discrete topology.
In the discrete topology case, all the norms are 1, by `norm_eq_one_iff_ne_zero_of_discrete`.
The nontrivially normed field instance is provided by a subtype with a proof that the
forgetful inheritance to the existing `NormedField` instance is definitionally true.
This allows one to have the new `NontriviallyNormedField` instance without data clashes. -/
lemma discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] :
    DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNormedField = h}) := by
  by_cases H : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    refine H.imp ?_
    -- contextual to reuse the `a ≠ 0` hypothesis in the proof of `a ≠ 0 ∧ ‖a‖ ≠ 1`
    simp +contextual [ne_of_lt]

lemma discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜]
    (h : BddAbove (Set.range fun k : 𝕜 ↦ ‖k‖)) :
    DiscreteTopology 𝕜 := by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

section Densely

variable (α) [DenselyNormedField α]

theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

section NontriviallyNormedField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℤ} {x : 𝕜}

@[simp]
protected lemma continuousAt_zpow : ContinuousAt (fun x ↦ x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n := by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).not_tendsto (Metric.disjoint_nhds_cobounded _)
    (tendsto_zpow_nhdsNE_zero_cobounded hm)

@[simp]
protected lemma continuousAt_inv : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)

end NontriviallyNormedField
end NormedField

instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]

instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section Complete

lemma NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedField K] :
    CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K) := by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨k, hk⟩ := hu.norm_bddAbove
  have kpos : 0 ≤ k := (_root_.norm_nonneg (u 0)).trans (hk (by simp))
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K k
  have hu' : CauchySeq ((· / x) ∘ u) := (uniformContinuous_div_const' x).comp_cauchySeq hu
  have hb : ∀ n, ((· / x) ∘ u) n ∈ Metric.closedBall 0 1 := by
    intro
    simp only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right, norm_div]
    rw [div_le_one (kpos.trans_lt hx)]
    exact hx.le.trans' (hk (by simp))
  obtain ⟨a, -, ha'⟩ := cauchySeq_tendsto_of_isComplete h hb hu'
  refine ⟨a * x, (((continuous_mul_right x).tendsto a).comp ha').congr ?_⟩
  have hx' : x ≠ 0 := by
    contrapose! hx
    simp [hx, kpos]
  simp [div_mul_cancel₀ _ hx']

end Complete
