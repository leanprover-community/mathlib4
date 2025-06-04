/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology


/-! # Metric structure on `α →ᵤ β` -/

section iSupMul

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}
  [CompleteLattice α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
lemma iSup_mul_le (u v : ι → α) :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun _ ↦ mul_le_mul' (le_iSup _ _) (le_iSup _ _)

@[to_additive]
lemma le_iInf_mul (u v : ι → α) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  iSup_mul_le (α := αᵒᵈ) _ _

@[to_additive]
lemma iSup₂_mul_le (u v : (i : ι) → κ i → α) :
    ⨆ (i) (j), u i j * v i j ≤ (⨆ (i) (j), u i j) * ⨆ (i) (j), v i j := by
  refine le_trans ?_ (iSup_mul_le _ _)
  gcongr
  exact iSup_mul_le _ _

@[to_additive]
lemma le_iInf₂_mul (u v : (i : ι) → κ i → α) :
    (⨅ (i) (j), u i j) * ⨅ (i) (j), v i j ≤ ⨅ (i) (j), u i j * v i j :=
  iSup₂_mul_le (α := αᵒᵈ) _ _

end iSupMul

theorem BoundedContinuousFunction.edist_eq_iSup {α β : Type*} [TopologicalSpace α]
    [PseudoMetricSpace β] {f g : BoundedContinuousFunction α β} :
    edist f g = ⨆ (x : α), edist (f x) (g x) := by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x

variable {α β γ : Type*}

open scoped UniformConvergence NNReal
open Filter Topology

namespace UniformFun

noncomputable instance [PseudoEMetricSpace β] : PseudoEMetricSpace (α →ᵤ β) where
  edist f g := ⨆ x, edist (f x) (g x)
  edist_self := by simp
  edist_comm := by simp [edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) ≤ ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ ↦ edist_triangle _ _ _
    _ ≤ (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist |>.eq_biInf]
    simp only [Function.comp_apply, UniformFun.gen, Set.mem_setOf_eq]
    refine le_antisymm ?_ <| iInf₂_mono ?_
    · refine iInf₂_mono' fun ε hε ↦ ?_
      obtain ⟨δ, hδ, hδε⟩ := exists_between hε
      exact ⟨δ, hδ, by simpa [iSup_lt_iff] using fun f g h ↦ ⟨δ, hδε, fun x ↦ (h x).le⟩⟩
    · simpa using fun ε hε f g h x ↦ (le_iSup _ x).trans_lt h

lemma edist_def [PseudoEMetricSpace β] (f g : α →ᵤ β) :
    edist f g = ⨆ x, edist (toFun f x) (toFun g x) :=
  rfl

noncomputable instance [EMetricSpace β] : EMetricSpace (α →ᵤ β) where
  eq_of_edist_eq_zero {f g} h := funext fun x ↦ eq_of_edist_eq_zero <| le_antisymm
    ((edist_def f g ▸ h) ▸ le_iSup (fun y ↦ edist (f y) (g y)) x) (zero_le _)

noncomputable instance [PseudoMetricSpace β] [BoundedSpace β] :
    PseudoMetricSpace (α →ᵤ β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ ↦ by
      have := BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
      refine (iSup_le fun x ↦ EMetric.edist_le_diam_of_mem ?_ ?_).trans_lt this |>.ne
      all_goals trivial)
    (fun _ _ ↦ by simp [edist_def, ENNReal.toReal_iSup (fun _ ↦ edist_ne_top _ _), dist_edist])

noncomputable instance [MetricSpace β] [BoundedSpace β] :
    MetricSpace (α →ᵤ β) where
  eq_of_dist_eq_zero {f g} h := by
    rw [dist_edist, ENNReal.toReal_eq_zero_iff] at h
    exact eq_of_edist_eq_zero <| h.resolve_right <| edist_ne_top f g

lemma lipschitzWith_iff [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : γ → α →ᵤ β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c, LipschitzWith K (fun x ↦ toFun (f x) c) := by
  simp [LipschitzWith, edist_def, forall_comm (α := α), toFun, ofFun]

open BoundedContinuousFunction in
@[simp]
lemma edist_ofFun_boundedContinuousFunction [PseudoMetricSpace β] [TopologicalSpace α]
    {f g : α →ᵇ β} :
    edist (ofFun f) (ofFun g) = edist f g := by
  simp [edist_def, edist_eq_iSup]

@[simp]
lemma edist_ofFun_continuousMap [PseudoMetricSpace β] [TopologicalSpace α] [CompactSpace α]
    {f g : C(α, β)} :
    edist (ofFun f) (ofFun g) = edist f g := by
  refine Eq.trans ?_ <| (ContinuousMap.isometryEquivBoundedOfCompact α β).edist_eq f g
  exact edist_ofFun_boundedContinuousFunction (f := ContinuousMap.equivBoundedOfCompact α β f)
    (g := ContinuousMap.equivBoundedOfCompact α β g)

lemma edist_continuousMapMk [PseudoMetricSpace β] [TopologicalSpace α] [CompactSpace α]
    {f g : α →ᵤ β} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) :
    edist (⟨_, hf⟩ : C(α, β)) ⟨_, hg⟩ = edist f g := by
  simp [← edist_ofFun_continuousMap]

end UniformFun

namespace UniformOnFun

variable {𝔖 𝔗 : Set (Set α)}

lemma uniformContinuous_ofFun_toFun [UniformSpace β] (h : ∀ s ∈ 𝔖, ∃ T ⊆ 𝔗, T.Finite ∧ s ⊆ ⋃₀ T) :
    UniformContinuous (ofFun 𝔗 ∘ toFun 𝔖 : (α →ᵤ[𝔗] β) → α →ᵤ[𝔖] β) := by
  simp only [UniformContinuous, UniformOnFun.uniformity_eq, iInf₂_comm (ι₂ := Set (β × β))]
  refine tendsto_iInf_iInf fun V ↦ tendsto_iInf_iInf fun hV ↦ ?_
  simp only [tendsto_iInf, tendsto_principal]
  intro s hs
  rw [Filter.Eventually]
  simp only [mem_biInf_principal]
  obtain ⟨T, hT𝔗, hT, hsT⟩ := h s hs
  use T, hT, hT𝔗
  intro f hf
  simp only [UniformOnFun.gen, Set.mem_iInter, Set.mem_setOf_eq, Function.comp_apply] at hf ⊢
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp <| hsT hx
  exact hf t ht x hxt

/-- Let `f : γ → α →ᵤ[𝔖] β`. If for every `s ∈ 𝔖` and for every `c ∈ s`, the fucntion
`fun x ↦ f x c` is Lipschitz (with Lipschitz constant depending on `s`), then `f` is continuous. -/
lemma continuous_of_forall_lipschitzWith [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
    {f : γ → α →ᵤ[𝔖] β} (K : Set α → ℝ≥0)
    (h : ∀ s ∈ 𝔖, ∀ c ∈ s, LipschitzWith (K s) (fun x ↦ toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  revert h
  congr! with h s hs
  refine LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

noncomputable instance {s : Set α} [PseudoEMetricSpace β] : PseudoEMetricSpace (α →ᵤ[{s}] β) where
  edist f g := ⨆ x ∈ s, edist (f x) (g x)
  edist_self := by simp
  edist_comm := by simp [edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x ∈ s, edist (f₁ x) (f₃ x) ≤ ⨆ x ∈ s, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup₂_mono fun _ _ ↦ edist_triangle _ _ _
    _ ≤ (⨆ x ∈ s, edist (f₁ x) (f₂ x)) + (⨆ x ∈ s, edist (f₂ x) (f₃ x)) := iSup₂_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    trans ⨅ ε > 0, Filter.principal {p | ⨆ x ∈ s, edist (p.1 x) (p.2 x) ≤ ε}
    · rw [UniformOnFun.uniformity_eq_of_basis β {s} uniformity_basis_edist_le]
      simp [UniformOnFun.gen, iSup_le_iff, toFun, ofFun]
    refine le_antisymm ?_ (iInf₂_mono ?_)
    · refine iInf₂_mono' fun ε hε ↦ ?_
      obtain ⟨δ, hδ, hδε⟩ := exists_between hε
      exact ⟨δ, hδ, by simpa [iSup_lt_iff] using fun f g h ↦ ⟨δ, hδε, h⟩⟩
    · simp only [gt_iff_lt, iSup_le_iff, Filter.le_principal_iff, Filter.mem_principal,
        Set.setOf_subset_setOf, Prod.forall]
      exact fun ε hε f g h x hx ↦ (le_iSup₂ (f := fun x _ ↦ edist (f x) (g x)) x hx).trans h.le

end UniformOnFun
