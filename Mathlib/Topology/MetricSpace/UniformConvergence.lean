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

theorem ContinuousMap.edist_eq_iSup {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    [PseudoMetricSpace β] {f g : C(α, β)} :
    edist f g = ⨆ (x : α), edist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]

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

lemma lipschitzOnWith_iff [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : γ → α →ᵤ β} {K : ℝ≥0}
    {s : Set γ} : LipschitzOnWith K f s ↔ ∀ c, LipschitzOnWith K (fun x ↦ toFun (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma lipschitzWith_eval [PseudoEMetricSpace β] (x : α) :
    LipschitzWith 1 (fun f : α →ᵤ β ↦ f x) := by
  intro f g
  simpa [edist_def] using le_iSup (fun y ↦ edist (toFun f y) (toFun g y)) x

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

/-- If `𝔖` and `𝔗` are families of sets in `α`, then the identity map
`(α →ᵤ[𝔗] β) → (α →ᵤ[𝔖] β)` is uniformly continuous if every `s ∈ 𝔖` is containined in a finite
union of elements of `𝔗`.

With more API around `Order.Ideal`, this could be phrased in that language instead. -/
lemma uniformContinuous_ofFun_toFun [UniformSpace β] (h : ∀ s ∈ 𝔖, ∃ T ⊆ 𝔗, T.Finite ∧ s ⊆ ⋃₀ T) :
    UniformContinuous (ofFun 𝔗 ∘ toFun 𝔖 : (α →ᵤ[𝔗] β) → α →ᵤ[𝔖] β) := by
  simp only [UniformContinuous, UniformOnFun.uniformity_eq, iInf₂_comm (ι₂ := Set (β × β))]
  refine tendsto_iInf_iInf fun V ↦ tendsto_iInf_iInf fun hV ↦ ?_
  simp only [tendsto_iInf, tendsto_principal, Filter.Eventually, mem_biInf_principal]
  intro s hs
  obtain ⟨T, hT𝔗, hT, hsT⟩ := h s hs
  refine ⟨T, hT, hT𝔗, fun f hf ↦ ?_⟩
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

open scoped ENNReal
noncomputable instance [Finite 𝔖] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (α →ᵤ[𝔖] β) where
  edist f g := ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)
  edist_self := by simp
  edist_comm := by simp [edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x ∈ ⋃₀ 𝔖, edist (f₁ x) (f₃ x) ≤ ⨆ x ∈ ⋃₀ 𝔖, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup₂_mono fun _ _ ↦ edist_triangle _ _ _
    _ ≤ (⨆ x ∈ ⋃₀ 𝔖, edist (f₁ x) (f₂ x)) + (⨆ x ∈ ⋃₀ 𝔖, edist (f₂ x) (f₃ x)) := iSup₂_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    trans ⨅ ε > 0, Filter.principal {p | ⨆ x ∈ ⋃₀ 𝔖, edist (p.1 x) (p.2 x) ≤ ε}
    · rw [UniformOnFun.uniformity_eq_of_basis β 𝔖 uniformity_basis_edist_le]
      simp [UniformOnFun.gen, iSup_le_iff, toFun, ofFun, iInf₂_comm (ι₂ := ℝ≥0∞),
        iInf_principal_finite ‹_›, Set.iInter_setOf, forall_comm (α := α)]
    refine le_antisymm ?_ (iInf₂_mono ?_)
    · refine iInf₂_mono' fun ε hε ↦ ?_
      obtain ⟨δ, hδ, hδε⟩ := exists_between hε
      exact ⟨δ, hδ, by simpa [iSup_lt_iff] using fun f g h ↦ ⟨δ, hδε, h⟩⟩
    · simp only [gt_iff_lt, iSup_le_iff, Filter.le_principal_iff, Filter.mem_principal,
        Set.setOf_subset_setOf, Prod.forall]
      exact fun ε hε f g h x hx ↦ (le_iSup₂ (f := fun x _ ↦ edist (f x) (g x)) x hx).trans h.le

variable [Finite 𝔖]

lemma edist_def [PseudoEMetricSpace β] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) :=
  rfl

lemma edist_def' [PseudoEMetricSpace β] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ s ∈ 𝔖, ⨆ x ∈ s, edist (toFun 𝔖 f x) (toFun 𝔖 g x) := by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

lemma lipschitzWith_iff [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : γ → α →ᵤ[𝔖] β}
    {K : ℝ≥0} : LipschitzWith K f ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzWith K (fun x ↦ toFun 𝔖 (f x) c) := by
  simp [LipschitzWith, edist_def, toFun, ofFun]
  tauto

lemma lipschitzOnWith_iff [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
    {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzOnWith K (fun x ↦ toFun 𝔖 (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma lipschitzWith_eval [PseudoEMetricSpace β] (x : α) (hx : x ∈ ⋃₀ 𝔖) :
    LipschitzWith 1 (fun f : α →ᵤ[𝔖] β ↦ toFun 𝔖 f x) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using
    le_iSup₂ (f := fun y _ ↦ edist (toFun 𝔖 f y) (toFun 𝔖 g y)) x hx

lemma lipschitzWith_one_ofFun_toFun [PseudoEMetricSpace β] :
    LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFun : (α →ᵤ β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _ _ ↦ UniformFun.lipschitzWith_eval _

lemma lipschitzWith_one_ofFun_toFun' [Finite 𝔗] [PseudoEMetricSpace β] (h : ⋃₀ 𝔖 ⊆ ⋃₀ 𝔗) :
    LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α →ᵤ[𝔗] β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun x hx ↦ lipschitzWith_eval x (h hx)

lemma lipschitzWith_restrict [PseudoEMetricSpace β] (s : Set α) (hs : s ∈ 𝔖)  :
    LipschitzWith 1 (UniformFun.ofFun ∘ s.restrict ∘ toFun 𝔖 : (α →ᵤ[𝔖] β) → (s →ᵤ β)) :=
  UniformFun.lipschitzWith_iff.mpr fun x ↦ lipschitzWith_eval _ ⟨s, hs, x.2⟩

noncomputable instance [PseudoMetricSpace β] [BoundedSpace β] :
    PseudoMetricSpace (α →ᵤ[𝔖] β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ ↦ by
      have := BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
      sorry)
      --refine (iSup_le fun x ↦ EMetric.edist_le_diam_of_mem ?_ ?_).trans_lt this |>.ne
      --all_goals trivial)
    (fun _ _ ↦ sorry)
      -- by simp [edist_def, ENNReal.toReal_iSup (fun _ ↦ edist_ne_top _ _), dist_edist])

noncomputable instance [MetricSpace β] [BoundedSpace β] :
    MetricSpace (α →ᵤ β) where
  eq_of_dist_eq_zero {f g} h := by
    rw [dist_edist, ENNReal.toReal_eq_zero_iff] at h
    exact eq_of_edist_eq_zero <| h.resolve_right <| edist_ne_top f g

--open BoundedContinuousFunction in @[simp]
--lemma edist_ofFun_boundedContinuousFunction [PseudoMetricSpace β] [TopologicalSpace α]
    --{f g : α →ᵇ β} :
    --edist (ofFun f) (ofFun g) = edist f g := by
  --simp [edist_def, edist_eq_iSup]

--@[simp]
--lemma edist_ofFun_continuousMap [PseudoMetricSpace β] [TopologicalSpace α] [CompactSpace α]
    --{f g : C(α, β)} :
    --edist (ofFun f) (ofFun g) = edist f g := by
  --refine Eq.trans ?_ <| (ContinuousMap.isometryEquivBoundedOfCompact α β).edist_eq f g
  --exact edist_ofFun_boundedContinuousFunction (f := ContinuousMap.equivBoundedOfCompact α β f)
    --(g := ContinuousMap.equivBoundedOfCompact α β g)

lemma edist_continuousRestrict [PseudoMetricSpace β] [TopologicalSpace α] {f g : α →ᵤ[𝔖] β}
    [CompactSpace (⋃₀ 𝔖)] (hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖))
    (hg : ContinuousOn (toFun 𝔖 g) (⋃₀ 𝔖)) :
    edist (⟨_, hf.restrict⟩ : C(⋃₀ 𝔖, β)) ⟨_, hg.restrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

lemma edist_continuousRestrict' [PseudoMetricSpace β] [TopologicalSpace α] {s : Set α}
    {f g : α →ᵤ[{s}] β} [CompactSpace s] (hf : ContinuousOn (toFun {s} f) s)
    (hg : ContinuousOn (toFun {s} g) s) :
    edist (⟨_, hf.restrict⟩ : C(s, β)) ⟨_, hg.restrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

end UniformOnFun
