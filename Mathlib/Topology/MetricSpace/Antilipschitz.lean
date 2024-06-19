/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

#align_import topology.metric_space.antilipschitz from "leanprover-community/mathlib"@"c8f305514e0d47dfaa710f5a52f0d21b588e6328"

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`AntilipschitzWith K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/


variable {α β γ : Type*}

open scoped NNReal ENNReal Uniformity Topology
open Set Filter Bornology

/-- We say that `f : α → β` is `AntilipschitzWith K` if for any two points `x`, `y` we have
`edist x y ≤ K * edist (f x) (f y)`. -/
def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)
#align antilipschitz_with AntilipschitzWith

theorem AntilipschitzWith.edist_lt_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
  (h x y).trans_lt <| ENNReal.mul_lt_top ENNReal.coe_ne_top (edist_ne_top _ _)
#align antilipschitz_with.edist_lt_top AntilipschitzWith.edist_lt_top

theorem AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y ≠ ⊤ :=
  (h.edist_lt_top x y).ne
#align antilipschitz_with.edist_ne_top AntilipschitzWith.edist_ne_top

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β}

theorem antilipschitzWith_iff_le_mul_nndist :
    AntilipschitzWith K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) := by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast
#align antilipschitz_with_iff_le_mul_nndist antilipschitzWith_iff_le_mul_nndist

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=
  antilipschitzWith_iff_le_mul_nndist
#align antilipschitz_with.le_mul_nndist AntilipschitzWith.le_mul_nndist
#align antilipschitz_with.of_le_mul_nndist AntilipschitzWith.of_le_mul_nndist

theorem antilipschitzWith_iff_le_mul_dist :
    AntilipschitzWith K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast
#align antilipschitz_with_iff_le_mul_dist antilipschitzWith_iff_le_mul_dist

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=
  antilipschitzWith_iff_le_mul_dist
#align antilipschitz_with.le_mul_dist AntilipschitzWith.le_mul_dist
#align antilipschitz_with.of_le_mul_dist AntilipschitzWith.of_le_mul_dist

namespace AntilipschitzWith

theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) :
    K⁻¹ * nndist x y ≤ nndist (f x) (f y) := by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)
#align antilipschitz_with.mul_le_nndist AntilipschitzWith.mul_le_nndist

theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) := mod_cast hf.mul_le_nndist x y
#align antilipschitz_with.mul_le_dist AntilipschitzWith.mul_le_dist

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {f : α → β}

open EMetric

-- uses neither `f` nor `hf`
/-- Extract the constant from `hf : AntilipschitzWith K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unusedArguments]
protected def k (_hf : AntilipschitzWith K f) : ℝ≥0 := K
set_option linter.uppercaseLean3 false in
#align antilipschitz_with.K AntilipschitzWith.k

protected theorem injective {α : Type*} {β : Type*} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) : Function.Injective f := fun x y h => by
  simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y
#align antilipschitz_with.injective AntilipschitzWith.injective

theorem mul_le_edist (hf : AntilipschitzWith K f) (x y : α) :
    (K : ℝ≥0∞)⁻¹ * edist x y ≤ edist (f x) (f y) := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)
#align antilipschitz_with.mul_le_edist AntilipschitzWith.mul_le_edist

theorem ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) : diam (f ⁻¹' s) ≤ K * diam s :=
  diam_le fun x hx y hy => (hf x y).trans <|
    mul_le_mul_left' (edist_le_diam_of_mem (mem_preimage.1 hx) hy) K
#align antilipschitz_with.ediam_preimage_le AntilipschitzWith.ediam_preimage_le

theorem le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) : diam s ≤ K * diam (f '' s) :=
  (diam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))
#align antilipschitz_with.le_mul_ediam_image AntilipschitzWith.le_mul_ediam_image

protected theorem id : AntilipschitzWith 1 (id : α → α) := fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]
#align antilipschitz_with.id AntilipschitzWith.id

theorem comp {Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0} {f : α → β}
    (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g ∘ f) := fun x y =>
  calc
    edist x y ≤ Kf * edist (f x) (f y) := hf x y
    _ ≤ Kf * (Kg * edist (g (f x)) (g (f y))) := ENNReal.mul_left_mono (hg _ _)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]; rfl
#align antilipschitz_with.comp AntilipschitzWith.comp

theorem restrict (hf : AntilipschitzWith K f) (s : Set α) : AntilipschitzWith K (s.restrict f) :=
  fun x y => hf x y
#align antilipschitz_with.restrict AntilipschitzWith.restrict

theorem codRestrict (hf : AntilipschitzWith K f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    AntilipschitzWith K (s.codRestrict f hs) := fun x y => hf x y
#align antilipschitz_with.cod_restrict AntilipschitzWith.codRestrict

theorem to_rightInvOn' {s : Set α} (hf : AntilipschitzWith K (s.restrict f)) {g : β → α}
    {t : Set β} (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) :
    LipschitzWith K (t.restrict g) := fun x y => by
  simpa only [restrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_eq, Subtype.coe_mk] using
    hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩
#align antilipschitz_with.to_right_inv_on' AntilipschitzWith.to_rightInvOn'

theorem to_rightInvOn (hf : AntilipschitzWith K f) {g : β → α} {t : Set β} (h : RightInvOn g f t) :
    LipschitzWith K (t.restrict g) :=
  (hf.restrict univ).to_rightInvOn' (mapsTo_univ g t) h
#align antilipschitz_with.to_right_inv_on AntilipschitzWith.to_rightInvOn

theorem to_rightInverse (hf : AntilipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    LipschitzWith K g := by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this
#align antilipschitz_with.to_right_inverse AntilipschitzWith.to_rightInverse

theorem comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f f) ≤ 𝓤 α := by
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => ?_
  refine ⟨(↑K)⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', ?_⟩
  refine fun x hx => (hf x.1 x.2).trans_lt ?_
  rw [mul_comm, ← div_eq_mul_inv] at hx
  rw [mul_comm]
  exact ENNReal.mul_lt_of_lt_div hx
#align antilipschitz_with.comap_uniformity_le AntilipschitzWith.comap_uniformity_le

protected theorem uniformInducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    UniformInducing f :=
  ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩
#align antilipschitz_with.uniform_inducing AntilipschitzWith.uniformInducing

protected theorem uniformEmbedding {α : Type*} {β : Type*} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    UniformEmbedding f :=
  ⟨hf.uniformInducing hfc, hf.injective⟩
#align antilipschitz_with.uniform_embedding AntilipschitzWith.uniformEmbedding

theorem isComplete_range [CompleteSpace α] (hf : AntilipschitzWith K f)
    (hfc : UniformContinuous f) : IsComplete (range f) :=
  (hf.uniformInducing hfc).isComplete_range
#align antilipschitz_with.is_complete_range AntilipschitzWith.isComplete_range

theorem isClosed_range {α β : Type*} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
    {f : α → β} {K : ℝ≥0} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosed (range f) :=
  (hf.isComplete_range hfc).isClosed
#align antilipschitz_with.is_closed_range AntilipschitzWith.isClosed_range

theorem closedEmbedding {α : Type*} {β : Type*} [EMetricSpace α] [EMetricSpace β] {K : ℝ≥0}
    {f : α → β} [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    ClosedEmbedding f :=
  { (hf.uniformEmbedding hfc).embedding with isClosed_range := hf.isClosed_range hfc }
#align antilipschitz_with.closed_embedding AntilipschitzWith.closedEmbedding

theorem subtype_coe (s : Set α) : AntilipschitzWith 1 ((↑) : s → α) :=
  AntilipschitzWith.id.restrict s
#align antilipschitz_with.subtype_coe AntilipschitzWith.subtype_coe

@[nontriviality] -- Porting note: added `nontriviality`
theorem of_subsingleton [Subsingleton α] {K : ℝ≥0} : AntilipschitzWith K f := fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]
#align antilipschitz_with.of_subsingleton AntilipschitzWith.of_subsingleton

/-- If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`. -/
protected theorem subsingleton {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : AntilipschitzWith 0 f) : Subsingleton α :=
  ⟨fun x y => edist_le_zero.1 <| (h x y).trans_eq <| zero_mul _⟩
#align antilipschitz_with.subsingleton AntilipschitzWith.subsingleton

end AntilipschitzWith

namespace AntilipschitzWith

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : ℝ≥0} {f : α → β}

theorem isBounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounded s) :
    IsBounded (f ⁻¹' s) :=
  isBounded_iff_ediam_ne_top.2 <| ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top) (hf.ediam_preimage_le _)
#align antilipschitz_with.bounded_preimage AntilipschitzWith.isBounded_preimage

theorem tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (cobounded β) :=
  compl_surjective.forall.2 fun _ ↦ hf.isBounded_preimage
#align antilipschitz_with.tendsto_cobounded AntilipschitzWith.tendsto_cobounded

/-- The image of a proper space under an expanding onto map is proper. -/
protected theorem properSpace {α : Type*} [MetricSpace α] {K : ℝ≥0} {f : α → β} [ProperSpace α]
    (hK : AntilipschitzWith K f) (f_cont : Continuous f) (hf : Function.Surjective f) :
    ProperSpace β := by
  refine ⟨fun x₀ r => ?_⟩
  let K := f ⁻¹' closedBall x₀ r
  have A : IsClosed K := isClosed_ball.preimage f_cont
  have B : IsBounded K := hK.isBounded_preimage isBounded_closedBall
  have : IsCompact K := isCompact_iff_isClosed_bounded.2 ⟨A, B⟩
  convert this.image f_cont
  exact (hf.image_preimage _).symm
#align antilipschitz_with.proper_space AntilipschitzWith.properSpace

theorem isBounded_of_image2_left (f : α → β → γ) {K₁ : ℝ≥0}
    (hf : ∀ b, AntilipschitzWith K₁ fun a => f a b) {s : Set α} {t : Set β}
    (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t := by
  contrapose! hst
  obtain ⟨b, hb⟩ : t.Nonempty := nonempty_of_not_isBounded hst.2
  have : ¬IsBounded (Set.image2 f s {b}) := by
    intro h
    apply hst.1
    rw [Set.image2_singleton_right] at h
    replace h := (hf b).isBounded_preimage h
    exact h.subset (subset_preimage_image _ _)
  exact mt (IsBounded.subset · (image2_subset subset_rfl (singleton_subset_iff.mpr hb))) this
#align antilipschitz_with.bounded_of_image2_left AntilipschitzWith.isBounded_of_image2_left

theorem isBounded_of_image2_right {f : α → β → γ} {K₂ : ℝ≥0} (hf : ∀ a, AntilipschitzWith K₂ (f a))
    {s : Set α} {t : Set β} (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t :=
  Or.symm <| isBounded_of_image2_left (flip f) hf <| image2_swap f s t ▸ hst
#align antilipschitz_with.bounded_of_image2_right AntilipschitzWith.isBounded_of_image2_right

end AntilipschitzWith

theorem LipschitzWith.to_rightInverse [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0}
    {f : α → β} (hf : LipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    AntilipschitzWith K g := fun x y => by simpa only [hg _] using hf (g x) (g y)
#align lipschitz_with.to_right_inverse LipschitzWith.to_rightInverse

/-- The preimage of a proper space under a Lipschitz homeomorphism is proper. -/
protected theorem LipschitzWith.properSpace [PseudoMetricSpace α] [MetricSpace β] [ProperSpace β]
    {K : ℝ≥0} {f : α ≃ₜ β} (hK : LipschitzWith K f) : ProperSpace α :=
  (hK.to_rightInverse f.right_inv).properSpace f.symm.continuous f.symm.surjective
#align lipschitz_with.proper_space LipschitzWith.properSpace
