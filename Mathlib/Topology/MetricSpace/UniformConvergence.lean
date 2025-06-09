/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Metric structure on `α →ᵤ β` and `α →ᵤ[𝔖] β` for finite `𝔖`

When `β` is a (pseudo, extended) metric space it is a uniform space, and therefore we may
consider the type `α →ᵤ β` of functions equipped with the topology of uniform convergence. The
natural (pseudo, extended) metric on this space is given by `fun f g ↦ ⨆ x, edist (f x) (g x)`,
and this induces the existing uniformity. Unless `β` is a bounded space, this will not be a (pseudo)
metric space (except in the trivial case where `α` is empty).

When `𝔖 : Set (Set α)` is a collection of subsets, we may equip the space of functions with the
(pseudo, extended) metric `fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. *However*, this only induces
the pre-existing uniformity on `α →ᵤ[𝔖] β` if `𝔖` is finite, and hence we only have an instance in
that case. Nevertheless, this still covers the most important case, such as when `𝔖` is a singleton.

Furthermore, we note that this is essentially a mathematical obstruction, not a technical one:
indeed, the uniformity of `α →ᵤ[𝔖] β` is countably generated only when there is a sequence
`t : ℕ → Finset (Set α)` such that, for each `n`, `t n ⊆ 𝔖`, `fun n ↦ Finset.sup (t n)` is monotone
and for every `s ∈ 𝔖`, there is some `n` such that `s ⊆ Finset.sup (t n)` (see
`UniformOnFun.isCountablyGenerated_uniformity`). So, while the `𝔖` for which `α →ᵤ[𝔖] β` is
metrizable include some non-finite `𝔖`, there are some `𝔖` which are not metrizable, and moreover,
it is only when `𝔖` is finite that `⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)` is a metric which induces the
uniformity.

There are a few advantages of equipping this space with this metric structure.

1. A function `f : X → α →ᵤ β` is Lipschitz in this metric if and only if for every `a : α` it is
  Lipschitz in the first variable with the same Lipschitz constant.
2. It provides a natural setting in which one can talk about the metrics on `α →ᵇ β` or, when
  `α` is compact, `C(α, β)`, relative to their underlying bare functions.
-/

variable {α β γ : Type*} [PseudoEMetricSpace γ]
open scoped UniformConvergence NNReal ENNReal
open Filter Topology

namespace UniformFun

section EMetric

variable [PseudoEMetricSpace β]

/-- The natural `EMetric` structure on `α →ᵤ β` given by `edist f g = ⨆ x, edist (f x) (g x)`. -/
noncomputable instance : PseudoEMetricSpace (α →ᵤ β) where
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

lemma edist_def (f g : α →ᵤ β) :
    edist f g = ⨆ x, edist (toFun f x) (toFun g x) :=
  rfl

noncomputable instance {β : Type*} [EMetricSpace β] : EMetricSpace (α →ᵤ β) where
  eq_of_edist_eq_zero {f g} h := funext fun x ↦ eq_of_edist_eq_zero <| le_antisymm
    ((edist_def f g ▸ h) ▸ le_iSup (fun y ↦ edist (f y) (g y)) x) (zero_le _)

lemma lipschitzWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c, LipschitzWith K (fun x ↦ toFun (f x) c) := by
  simp [LipschitzWith, edist_def, forall_comm (α := α), toFun, ofFun]

lemma lipschitzWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} :
    LipschitzWith K (fun x ↦ ofFun (f x)) ↔ ∀ c, LipschitzWith K (f · c) :=
  lipschitzWith_iff

/-- If `f : α → γ → β` is a family of a functions, all of which are Lipschitz with the
same constant, then the family is uniformly equicontinuous. -/
lemma _root_.LipschitzWith.uniformEquicontinuous (f : α → γ → β) (K : ℝ≥0)
    (h : ∀ c, LipschitzWith K (f c)) : UniformEquicontinuous f := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous

lemma lipschitzOnWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c, LipschitzOnWith K (fun x ↦ toFun (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma lipschitzWith_eval (x : α) :
    LipschitzWith 1 (fun f : α →ᵤ β ↦ f x) := by
  intro f g
  simpa [edist_def] using le_iSup (fun y ↦ edist (toFun f y) (toFun g y)) x

end EMetric

section Metric

variable [PseudoMetricSpace β]

noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ ↦ by
      have := BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
      refine (iSup_le fun x ↦ EMetric.edist_le_diam_of_mem ?_ ?_).trans_lt this |>.ne
      all_goals trivial)
    (fun _ _ ↦ by simp [edist_def, ENNReal.toReal_iSup (fun _ ↦ edist_ne_top _ _), dist_edist])

noncomputable instance [BoundedSpace β] : BoundedSpace (α →ᵤ β) where
  bounded_univ := by
    rw [Metric.isBounded_iff_ediam_ne_top, ← lt_top_iff_ne_top]
    refine lt_of_le_of_lt ?_ <| BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
    simp only [EMetric.diam_le_iff, Set.mem_univ, edist_def, iSup_le_iff, forall_const]
    exact fun f g x ↦ EMetric.edist_le_diam_of_mem (by trivial) (by trivial)

noncomputable instance {β : Type*} [MetricSpace β] [BoundedSpace β] : MetricSpace (α →ᵤ β) where
  eq_of_dist_eq_zero {f g} h := by
    rw [dist_edist, ENNReal.toReal_eq_zero_iff] at h
    exact eq_of_edist_eq_zero <| h.resolve_right <| edist_ne_top f g

open BoundedContinuousFunction in
lemma isometry_ofFun_boundedContinuousFunction [TopologicalSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : (α →ᵇ β) → α →ᵤ β) := by
  simp [Isometry, edist_def, edist_eq_iSup]

lemma isometry_ofFun_continuousMap [TopologicalSpace α] [CompactSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : C(α, β) → α →ᵤ β) :=
  isometry_ofFun_boundedContinuousFunction.comp <|
    ContinuousMap.isometryEquivBoundedOfCompact α β |>.isometry

lemma edist_continuousMapMk [TopologicalSpace α] [CompactSpace α]
    {f g : α →ᵤ β} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) :
    edist (⟨_, hf⟩ : C(α, β)) ⟨_, hg⟩ = edist f g := by
  simp [← isometry_ofFun_continuousMap.edist_eq]

end Metric

end UniformFun

namespace UniformOnFun

variable {𝔖 𝔗 : Set (Set α)}

section EMetric

variable [PseudoEMetricSpace β]

/-- Let `f : γ → α →ᵤ[𝔖] β`. If for every `s ∈ 𝔖` and for every `c ∈ s`, the fucntion
`fun x ↦ f x c` is Lipschitz (with Lipschitz constant depending on `s`), then `f` is continuous. -/
lemma continuous_of_forall_lipschitzWith {f : γ → α →ᵤ[𝔖] β} (K : Set α → ℝ≥0)
    (h : ∀ s ∈ 𝔖, ∀ c ∈ s, LipschitzWith (K s) (fun x ↦ toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  revert h
  congr! with h s hs
  refine LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

variable [Finite 𝔖]

noncomputable instance : PseudoEMetricSpace (α →ᵤ[𝔖] β) where
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

lemma edist_def (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) :=
  rfl

lemma edist_def' (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ s ∈ 𝔖, ⨆ x ∈ s, edist (toFun 𝔖 f x) (toFun 𝔖 g x) := by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

lemma lipschitzWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzWith K (fun x ↦ toFun 𝔖 (f x) c) := by
  simp [LipschitzWith, edist_def, toFun, ofFun]
  tauto

lemma lipschitzOnWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzOnWith K (fun x ↦ toFun 𝔖 (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma lipschitzWith_eval (x : α) (hx : x ∈ ⋃₀ 𝔖) :
    LipschitzWith 1 (fun f : α →ᵤ[𝔖] β ↦ toFun 𝔖 f x) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using
    le_iSup₂ (f := fun y _ ↦ edist (toFun 𝔖 f y) (toFun 𝔖 g y)) x hx

lemma lipschitzWith_one_ofFun_toFun :
    LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFun : (α →ᵤ β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _ _ ↦ UniformFun.lipschitzWith_eval _

lemma lipschitzWith_one_ofFun_toFun' [Finite 𝔗] (h : ⋃₀ 𝔖 ⊆ ⋃₀ 𝔗) :
    LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α →ᵤ[𝔗] β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun x hx ↦ lipschitzWith_eval x (h hx)

lemma lipschitzWith_restrict (s : Set α) (hs : s ∈ 𝔖)  :
    LipschitzWith 1 (UniformFun.ofFun ∘ s.restrict ∘ toFun 𝔖 : (α →ᵤ[𝔖] β) → (s →ᵤ β)) :=
  UniformFun.lipschitzWith_iff.mpr fun x ↦ lipschitzWith_eval _ ⟨s, hs, x.2⟩

lemma isometry_restrict (s : Set α) :
    Isometry (UniformFun.ofFun ∘ s.restrict ∘ toFun {s} : (α →ᵤ[{s}] β) → (s →ᵤ β)) := by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

end EMetric

section Metric

variable [Finite 𝔖] [PseudoMetricSpace β]

noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ[𝔖] β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ ↦ by
      have := BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
      refine (iSup₂_le fun x _ ↦ EMetric.edist_le_diam_of_mem ?_ ?_).trans_lt this |>.ne
      all_goals trivial)
    (fun _ _ ↦ by
      simp only [dist_edist, edist_def, iSup_sigma']
      rw [ENNReal.toReal_iSup]
      · congr!
        rw [ENNReal.toReal_iSup]
        exact (fun _ ↦ edist_ne_top _ _)
      · have := BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
        refine fun x ↦ lt_of_le_of_lt (iSup_le fun hx ↦ ?_) this |>.ne
        exact EMetric.edist_le_diam_of_mem (by trivial) (by trivial))

noncomputable instance [BoundedSpace β] : BoundedSpace (α →ᵤ[𝔖] β) where
  bounded_univ := by
    convert lipschitzWith_one_ofFun_toFun (𝔖 := 𝔖) (β := β) |>.isBounded_image (.all Set.univ)
    ext f
    simp only [Set.mem_univ, Function.comp_apply, Set.image_univ, Set.mem_range, true_iff]
    exact ⟨UniformFun.ofFun (toFun 𝔖 f), by simp⟩

lemma edist_continuousRestrict [TopologicalSpace α] {f g : α →ᵤ[𝔖] β}
    [CompactSpace (⋃₀ 𝔖)] (hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖))
    (hg : ContinuousOn (toFun 𝔖 g) (⋃₀ 𝔖)) :
    edist (⟨_, hf.restrict⟩ : C(⋃₀ 𝔖, β)) ⟨_, hg.restrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

lemma edist_continuousRestrict_of_singleton [TopologicalSpace α] {s : Set α}
    {f g : α →ᵤ[{s}] β} [CompactSpace s] (hf : ContinuousOn (toFun {s} f) s)
    (hg : ContinuousOn (toFun {s} g) s) :
    edist (⟨_, hf.restrict⟩ : C(s, β)) ⟨_, hg.restrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

end Metric

end UniformOnFun
