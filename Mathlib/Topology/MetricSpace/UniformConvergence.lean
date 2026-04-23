/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Uniformity

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

public section

variable {α β γ : Type*} [PseudoEMetricSpace γ]
open scoped UniformConvergence NNReal ENNReal
open Filter Topology Uniformity

namespace UniformFun

section EMetric

variable [PseudoEMetricSpace β]

noncomputable instance : EDist (α →ᵤ β) where
  edist f g := ⨆ x, edist (toFun f x) (toFun g x)

lemma edist_def (f g : α →ᵤ β) :
    edist f g = ⨆ x, edist (toFun f x) (toFun g x) :=
  rfl

lemma edist_le {f g : α →ᵤ β} {C : ℝ≥0∞} :
    edist f g ≤ C ↔ ∀ x, edist (toFun f x) (toFun g x) ≤ C :=
  iSup_le_iff

/-- The natural `EMetric` structure on `α →ᵤ β` given by `edist f g = ⨆ x, edist (f x) (g x)`. -/
noncomputable instance : PseudoEMetricSpace (α →ᵤ β) where
  edist_self := by simp [edist_def]
  edist_comm := by simp [edist_def, edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) ≤ ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ ↦ edist_triangle _ _ _
    _ ≤ (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    suffices 𝓤 (α →ᵤ β) = comap (fun x ↦ edist x.1 x.2) (𝓝 0) by
      simp [this, ENNReal.nhds_zero_basis.comap _ |>.eq_biInf, Set.Iio]
    rw [ENNReal.nhds_zero_basis_Iic.comap _ |>.eq_biInf]
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist_le |>.eq_biInf]
    simp [UniformFun.gen, edist_le, Set.Iic]

noncomputable instance {β : Type*} [EMetricSpace β] : EMetricSpace (α →ᵤ β) :=
  .ofT0PseudoEMetricSpace _

lemma lipschitzWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c, LipschitzWith K (fun x ↦ toFun (f x) c) := by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]

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

lemma lipschitzOnWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K (fun x ↦ ofFun (f x)) s ↔ ∀ c, LipschitzOnWith K (f · c) s :=
  lipschitzOnWith_iff

/-- If `f : α → γ → β` is a family of a functions, all of which are Lipschitz on `s` with the
same constant, then the family is uniformly equicontinuous on `s`. -/
lemma _root_.LipschitzOnWith.uniformEquicontinuousOn (f : α → γ → β) (K : ℝ≥0) {s : Set γ}
    (h : ∀ c, LipschitzOnWith K (f c) s) : UniformEquicontinuousOn f s := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn

lemma edist_eval_le {f g : α →ᵤ β} {x : α} :
    edist (toFun f x) (toFun g x) ≤ edist f g :=
  edist_le.mp le_rfl x

lemma lipschitzWith_eval (x : α) :
    LipschitzWith 1 (fun f : α →ᵤ β ↦ toFun f x) := by
  intro f g
  simpa using edist_eval_le

end EMetric

section Metric

variable [PseudoMetricSpace β]

noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ ↦ Real.iSup_nonneg fun i ↦ dist_nonneg)
    fun f g ↦ by
      cases isEmpty_or_nonempty α
      · simp [edist_def]
      have : BddAbove <| .range fun x ↦ dist (toFun f x) (toFun g x) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      exact ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ by simp [edist_def, ciSup_le_iff this]

lemma dist_def [BoundedSpace β] (f g : α →ᵤ β) :
    dist f g = ⨆ x, dist (toFun f x) (toFun g x) :=
  rfl

lemma dist_le [BoundedSpace β] {f g : α →ᵤ β} {C : ℝ} (hC : 0 ≤ C) :
    dist f g ≤ C ↔ ∀ x, dist (toFun f x) (toFun g x) ≤ C := by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]

noncomputable instance [BoundedSpace β] : BoundedSpace (α →ᵤ β) where
  bounded_univ := by
    rw [Metric.isBounded_iff_ediam_ne_top, ← lt_top_iff_ne_top]
    refine lt_of_le_of_lt ?_ <| BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
    simp only [Metric.ediam_le_iff, Set.mem_univ, edist_le, forall_const]
    exact fun f g x ↦ Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)

noncomputable instance {β : Type*} [MetricSpace β] [BoundedSpace β] : MetricSpace (α →ᵤ β) :=
  .ofT0PseudoMetricSpace _

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

/-- Let `f : γ → α →ᵤ[𝔖] β`. If for every `s ∈ 𝔖` and for every `c ∈ s`, the function
`fun x ↦ f x c` is Lipschitz (with Lipschitz constant depending on `s`), then `f` is continuous. -/
lemma continuous_of_forall_lipschitzWith {f : γ → α →ᵤ[𝔖] β} (K : Set α → ℝ≥0)
    (h : ∀ s ∈ 𝔖, ∀ c ∈ s, LipschitzWith (K s) (fun x ↦ toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs ↦ LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

@[nolint unusedArguments]
noncomputable instance [Finite 𝔖] : EDist (α →ᵤ[𝔖] β) where
  edist f g := ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x)

lemma edist_def [Finite 𝔖] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) :=
  rfl

lemma edist_def' [Finite 𝔖] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ s ∈ 𝔖, ⨆ x ∈ s, edist (toFun 𝔖 f x) (toFun 𝔖 g x) := by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

lemma edist_eq_restrict_sUnion [Finite 𝔖] {f g : α →ᵤ[𝔖] β} :
    edist f g = edist
      (UniformFun.ofFun ((⋃₀ 𝔖).restrict (toFun 𝔖 f)))
      (UniformFun.ofFun ((⋃₀ 𝔖).restrict (toFun 𝔖 g))) :=
  iSup_subtype'

lemma edist_eq_pi_restrict [Fintype 𝔖] {f g : α →ᵤ[𝔖] β} :
    edist f g = edist
      (fun s : 𝔖 ↦ UniformFun.ofFun ((s : Set α).restrict (toFun 𝔖 f)))
      (fun s : 𝔖 ↦ UniformFun.ofFun ((s : Set α).restrict (toFun 𝔖 g))) := by
  simp_rw [edist_def', iSup_subtype', edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

variable [Finite 𝔖]

/-- The natural `EMetric` structure on `α →ᵤ[𝔖] β` when `𝔖` is finite given by
`edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. -/
noncomputable instance : PseudoEMetricSpace (α →ᵤ[𝔖] β) where
  edist_self f := by simp [edist_eq_restrict_sUnion]
  edist_comm := by simp [edist_eq_restrict_sUnion, edist_comm]
  edist_triangle f₁ f₂ f₃ := by simp [edist_eq_restrict_sUnion, edist_triangle]
  toUniformSpace := inferInstance
  uniformity_edist := by
    let _ := Fintype.ofFinite 𝔖;
    simp_rw [← isUniformInducing_pi_restrict.comap_uniformity,
      PseudoEMetricSpace.uniformity_edist, comap_iInf, comap_principal, edist_eq_pi_restrict,
      Set.preimage_setOf_eq]

lemma edist_le {f g : α →ᵤ[𝔖] β} {C : ℝ≥0∞} :
    edist f g ≤ C ↔ ∀ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) ≤ C := by
  simp_rw [edist_def, iSup₂_le_iff]

lemma lipschitzWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzWith K (fun x ↦ toFun 𝔖 (f x) c) := by
  simp [LipschitzWith, edist_le]
  tauto

lemma lipschitzOnWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzOnWith K (fun x ↦ toFun 𝔖 (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma edist_eval_le {f g : α →ᵤ[𝔖] β} {x : α} (hx : x ∈ ⋃₀ 𝔖) :
    edist (toFun 𝔖 f x) (toFun 𝔖 g x) ≤ edist f g :=
  edist_le.mp le_rfl x hx

lemma lipschitzWith_eval {x : α} (hx : x ∈ ⋃₀ 𝔖) :
    LipschitzWith 1 (fun f : α →ᵤ[𝔖] β ↦ toFun 𝔖 f x) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using edist_eval_le hx

lemma lipschitzWith_one_ofFun_toFun :
    LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFun : (α →ᵤ β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _ _ ↦ UniformFun.lipschitzWith_eval _

lemma lipschitzWith_one_ofFun_toFun' [Finite 𝔗] (h : ⋃₀ 𝔖 ⊆ ⋃₀ 𝔗) :
    LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α →ᵤ[𝔗] β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _x hx ↦ lipschitzWith_eval (h hx)

lemma lipschitzWith_restrict (s : Set α) (hs : s ∈ 𝔖) :
    LipschitzWith 1 (UniformFun.ofFun ∘ s.restrict ∘ toFun 𝔖 : (α →ᵤ[𝔖] β) → (s →ᵤ β)) :=
  UniformFun.lipschitzWith_iff.mpr fun x ↦ lipschitzWith_eval ⟨s, hs, x.2⟩

lemma isometry_restrict (s : Set α) :
    Isometry (UniformFun.ofFun ∘ s.restrict ∘ toFun {s} : (α →ᵤ[{s}] β) → (s →ᵤ β)) := by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

end EMetric

section Metric

variable [Finite 𝔖] [PseudoMetricSpace β]

noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ[𝔖] β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x : ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ ↦ Real.iSup_nonneg fun i ↦ dist_nonneg)
    fun f g ↦ by
      cases isEmpty_or_nonempty (⋃₀ 𝔖)
      · simp_all [edist_def]
      have : BddAbove (.range fun x : ⋃₀ 𝔖 ↦ dist (toFun 𝔖 f x) (toFun 𝔖 g x)) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
      simp [edist_def, ciSup_le_iff this]

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
